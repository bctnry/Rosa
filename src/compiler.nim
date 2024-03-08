import std/tables
import std/options
import ast
import vm
import transform/transform
import prettyprint
from std/enumerate import enumerate
from std/strformat import `&`


proc collectConst(x: seq[(string, int)]): TableRef[string, int] =
  var res = newTable[string, int]()
  for v in x:
    res[v[0]] = v[1]
  return res
  
type
  EnvFrame = tuple
    constTable: TableRef[string, int]
    globalTable: TableRef[string, int]
    varTable: TableRef[string, int]
    procTable: TableRef[string, tuple[loc: int, arity: int]]
    argTable: TableRef[string, int]
  Env = seq[EnvFrame]
  
proc allocVar(x: seq[string]): TableRef[string, int] =
  var res = newTable[string, int]()
  for (i, v) in enumerate(x):
    res[v] = i
  return res

# NOTE: for args #0, #1, #2, ..., #n-1 we assign offset -(n), -(n-1), ..., -1
# since base pointer points to the static link field.
proc assignParams(x: ProcDef): TableRef[string, int] =
  var res = newTable[string, int]()
  let paramLen = x.paramList.len
  var i = -paramLen
  for v in x.paramList:
    res[v] = i
    i += 1
  return res

# NOTE: this looks up argTable as well.
proc lookupVar(name: string, env: Env): Option[int] =
  var i = env.len()-1
  while i >= 0:
    var t = env[i].varTable
    if t != nil and t.hasKey(name): return some(t[name])
    t = env[i].argTable
    if t != nil and t.hasKey(name): return some(t[name])
    i -= 1
    continue
  return none(int)

proc lookupGlobal(name: string, env: Env): Option[int] =
  var i = env.len()-1
  while i >= 0:
    var t = env[i].globalTable
    if t != nil and t.hasKey(name): return some(t[name])
    t = env[i].argTable
    if t != nil and t.hasKey(name): return some(t[name])
    i -= 1
    continue
  return none(int)

proc lookupProc(env: Env, name: string): Option[tuple[loc: int, arity: int]] =
  var i = env.len()-1
  while i >= 0:
    let t = env[i].procTable
    if t == nil:
      i -= 1
      continue
    if not t.hasKey(name):
      i -= 1
      continue
    return some(t[name])
  return none(tuple[loc: int, arity: int])

proc lookupConst(name: string, env: Env): Option[int] =
  var i = env.len()-1
  while i >= 0:
    let t = env[i].constTable
    if t == nil:
      i -= 1
      continue
    if not t.hasKey(name):
      i -= 1
      continue
    return some(t[name])
  return none(int)

proc compileExpr(x: Expr, env: Env): seq[Instr] =
  var res: seq[Instr] = @[]
  block dispatch:
    case x.eType:
      of E_BINOP:
        res &= x.bLhs.compileExpr(env)
        res &= x.bRhs.compileExpr(env)
        let opNum = case x.binop:
                      of "+": 2
                      of "-": 3
                      of "*": 4
                      of "/": 5
                      else: -1  # cannot happen
        res.add((OPR, opNum))
      of E_UNARYOP:
        # NOTE: "ref" needs to be handled differently since when taking the
        # ref of a variable we don't actually evaluate that variable.
        if x.uOp == "ref":
          # now we extract the variable name. due to how we handle the
          # parsing we won't have anything but ast for variable here.
          assert(x.uBody.eType == E_VAR)
          var lookupRes = lookupVar(x.uBody.vName, env)
          if lookupRes.isNone():
            x.raiseErrorWithReason(&"Variable {x.uBody.vName} is not defined.")
            res.add((REF, lookupRes.get()))
          else:
            res &= x.uBody.compileExpr(env)
            case x.uOp:
              of "-":
                res.add((OPR, 1))
              of "valof":
                res.add((DEREF, 0))
              else:
                discard  # cannot happen.
        else:
          res &= x.uBody.compileExpr(env)
          case x.uOp:
            of "-":
              res.add((OPR, 1))
            of "valof":
              res.add((DEREF, 0))
            else:
              discard  # cannot happen.
      of E_LIT:
        res.add((LIT, x.lVal))
      of E_VAR:
        var lookupRes = lookupVar(x.vName, env)
        if lookupRes.isSome():
          res.add((LOD, lookupRes.get()))
          break dispatch
        lookupRes = lookupGlobal(x.vName, env)
        if lookupRes.isSome():
          res.add((LODA, lookupRes.get()))
          break dispatch
        lookupRes = lookupConst(x.vName, env)
        if lookupRes.isSome():
          res.add((LIT, lookupRes.get()))
          break dispatch
        x.raiseErrorWithReason(&"Cannot find the definition of {x.vName}")
  echo "res ", x, res
  return res

proc compileCond(x: Cond, env: Env): seq[Instr] =
  var res: seq[Instr] = @[]
  case x.cType:
    of C_EXPR_PRED:
      res &= x.pBody.compileExpr(env)
      let opNum = case x.predName:
                    of "odd": 6
                    else: -1
      res.add((OPR, opNum))
    of C_EXPR_REL:
      res &= x.relLhs.compileExpr(env)
      res &= x.relRhs.compileExpr(env)
      let opNum = case x.relOp:
                    of "=": 8
                    of "#": 9
                    of "<=": 11
                    of ">=": 13
                    of "<": 10
                    of ">": 12
                    else: -1  # cannot happen
      res.add((OPR, opNum))
  return res

# Now this gets slightly tricky. The branching instruction in the vm of the original
# PL/0 uses absolute address while it's more common to have offsets for branching
# instructions. To compile things with absolute address we need to know the actual
# location of a lot of things. Consider this example:
#
#   if a > 3 then
#   begin
#     a := 3;
#   end;
#
# One shall compile this into:
#
#       LOD (a)
#       LIT 0, 3
#       OPR 0, 12
#       JPC 0, L1
#       LIT 0, 3
#       STO (a)
#   L1:
#
# (Notice that JPC jumps when the stacktop is 0, i.e. condition not satisfied)
# If JPC takes an offset as its argument then it can be resolved recursively
# without knowing where exactly L1 would be, since the offset would be only
# related to the length of the branch body. Also consider this example:
#
#   while a < 5 do
#   begin
#     a := a + 2;
#   end;
#
# This shall be compiled into:
#
#   L1: LOD (a)
#       LIT 0, 5
#       OPR 0, 10
#       JPC 0, L2
# 
#       LOD (a)
#       LIT 0, 2
#       OPR 0, 2
#       STO (a)
#       JMP 0, L1
#   L2:
#
# Not only do we need to know where L2 is, we also need to know where L1 is now. 

# Now I shall explain why the return type is (seq[Instr], seq[int]): this is to
# support mutual recursion. To compile a CALL statement that refers to a
# procedure that happens later in the source code, one must first know its
# location; but to know its location we must compile everything because we need
# to do that to work out the size and from the size the location; it's a mutual
# dependent situation. The solution taken here is to first compile everything
# but with placeholder CAL instructions and to fill in the actual value later.
# the `seq[(int, int, string)]` part is for returning the location of such
# instructions and the name of the called procedures. The second `int` part is
# to maintain the proper layer count; this will become relevant in later parts.
proc compileStatementList(x: seq[Statement], currentLoc: int, env: Env): (seq[Instr], seq[(int, int, string)])
proc compileStatement(x: Statement, currentLoc: int, env: Env): (seq[Instr], seq[(int, int, string)]) =
  var res: seq[Instr] = @[]
  var callFillers: seq[(int, int, string)] = @[]
  case x.sType:
    of S_ASSIGN:
      block dispatch:
        case x.aTarget.lvType:
          of LV_VAR:
            var resolveRes = lookupVar(x.aTarget.vName, env)
            if resolveRes.isSome():
              res &= x.aVal.compileExpr(env)
              res.add((STO, resolveRes.get()))
              break dispatch
            resolveRes = lookupGlobal(x.aTarget.vName, env)
            if resolveRes.isSome():
              res &= x.aVal.compileExpr(env)
              res.add((STOA, resolveRes.get()))
              break dispatch
            x.raiseErrorWithReason(&"Variable name {x.aTarget.vName} not found.")
          of LV_DEREF:
            res &= x.aVal.compileExpr(env)
            var lhsRes = x.aTarget.drBody.compileExpr(env)
            # NOTE: this is a little complicated to explain. Consider the lhs `A[]`,
            # we would expect the value of `A` to be on top of the stack; with the
            # lhs `A[][]`, this value should be `valof A`; with lhs `A[][][]`, this
            # value should be `valof valof A`; etc.. A way to reuse currently-existing
            # code is to treat `[]` as `valof`, compile the whole thing as an expr,
            # and remove the last `valof` operation (which compiles to a single
            # `DEREF` instruction.
            assert(lhsRes[^1][0] == DEREF)
            discard lhsRes.pop()
            res &= lhsRes
            res.add((POPA, 0))
            res.add((POPR, 0))
    of S_BLOCK:
      let s = compileStatementList(x.body, currentLoc, env)
      res &= s[0]
      callFillers &= s[1]
    of S_IF:
      let condPart: seq[Instr] = compileCond(x.ifCond, env)
      res &= condPart
      # the `+1` is for the JPC instr itself; it's the same case for S_WHILE.
      let bodyPart = compileStatement(x.ifThen, currentLoc + condPart.len + 1, env)
      let bodyInstr = bodyPart[0]
      let bodyCallFillers = bodyPart[1]
      res.add((JPC, currentLoc + condPart.len() + 1 + bodyInstr.len()))
      res &= bodyInstr
      callFillers &= bodyCallFillers
    of S_WHILE:
      let l1 = currentLoc
      let condPart = compileCond(x.wCond, env)
      res &= condPart
      let bodyPart = compileStatement(x.wBody, currentLoc + condPart.len + 1, env)
      # the last `+1` part is for the JMP instruction used to jump back to L1.
      res.add((JPC, currentLoc + condPart.len + 1 + bodyPart[0].len + 1))
      res &= bodyPart[0]
      res.add((JMP, l1))
      callFillers &= bodyPart[1]
    of S_INPUT:
      res.add((OPR, 7))
      block dispatch:
        case x.iTarget.lvType:
          of LV_VAR:
            var resolveRes = lookupVar(x.iTarget.vName, env)
            if resolveRes.isSome():
              res.add((STO, resolveRes.get()))
              break dispatch
            resolveRes = lookupGlobal(x.iTarget.vName, env)
            if resolveRes.isSome():
              res.add((STOA, resolveRes.get()))
              break dispatch
            x.raiseErrorWithReason(&"Variable name {x.iTarget.vName} not found")
          of LV_DEREF:
            var lhsRes = x.iTarget.drBody.compileExpr(env)
            assert(lhsRes[^1][0] == DEREF)
            discard lhsRes.pop()
            res &= lhsRes
            res.add((POPA, 0))
            res.add((POPR, 0))
    of S_PRINT:
      res &= compileExpr(x.pExpr, env)
      res.add((OPR, 14))
    of S_RETURN:
      res &= compileExpr(x.rExpr, env)
      res.add((POPA, 0))
      res.add((OPR, 0))
    of S_CALL:
      let lookupRes = env.lookupProc(x.cTarget)
      if lookupRes.isSome():
        if lookupRes.get.arity != x.cArgs.len:
          x.raiseErrorWithReason("Arity mismatch.")
      var cnt = currentLoc
      if x.cArgs.len > 0:
        for a in x.cArgs:
          let argRes = compileExpr(a, env)
          res &= argRes
          cnt += argRes.len
      # inserting placeholder call instr.
      res.add((CAL, 0))
      callFillers.add((cnt, 0, x.cTarget))
      if x.cArgs.len > 0:
        for a in x.cArgs:
          res.add((POP, 0))
      # NOTE: PUSHA is not added since CALL statement does not use the return value.
      # TODO: we handle argument passing later.
      # NOTE: the info is only used for arity check because we don't know the
      # actual length of the procedures yet - we can only infer its function
      # signature before actually compiling them.
  return (res, callFillers)

proc compileStatementList(x: seq[Statement], currentLoc: int, env: Env): (seq[Instr], seq[(int, int, string)]) =
  var res: seq[Instr] = @[]
  var callFillers: seq[(int, int, string)] = @[]
  var cnt = currentLoc
  for stmt in x:
    let stmtRes = stmt.compileStatement(cnt, env)
    res &= stmtRes[0]
    callFillers &= stmtRes[1]
    cnt += stmtRes[0].len()
  return (res, callFillers)

# For every block we need to do the following things:
# 1.  Collect all constant definitions.
# 2.  Allocate variables.
# 3.  Compile all local procedures.
# 4.  Compile block body.
# The layout of the generated insructions would be:
#
#       INT 0, (size)
#       JMP 0, L1
#       (proc 1)
#       (proc 2)
#       (...)
#   L1: (body)
#       OPR 0, 0
#
# From this we know to insert the JMP instruction at the beginning we must know
# the proper location of L1; thus we need to first compile the local procedures
# first.
#
# Now this is very tricky. Do we allow local procedures calling other
# procedures defined in the "outside"? If so, we cannot truly resolve all the
# placeholder CAL instructions locally, thus if we start from the deepest level
# and work our way out we can only resolve a part of the CALs; more precisely,
# we can only resolve the part of CALs that refers to local procedures only.
# Consider the following example:
#
#   procedure A1;
#     procedure B1;
#     begin
#       call A2;  (* <-- point A *)
#     end;
#     procedure B2;
#     begin
#       call B1;  (* <-- point B *)
#     end;
#   begin
#     ! 4
#   end; 
#   procedure A2;
#   begin
#     ! 3
#   end;
#
#   begin
#     call A1;
#     call A2;
#   end.
#
# Procedure A1 would be compiled into:
#
#       JMP 0, Z0
#   A1: ;; (INT instruction ignored since there is no VAR defs in A1)
#       JMP 0, L1
#   B1: ;; (JMP ignored since there is no local procedure)
#       CAL ?, ?  ;; <-- point A
#       OPR 0, 0
#   B2: CAL ?, ?  ;; <-- point B
#       OPR 0, 0
#   L1: LIT 0, 4
#       OPR 0, 14
#       OPR 0, 0
#   A2: ;; (INT instruction ignored since there is no VAR defs in A2)
#       ;; (JMP instruction ignored since there is no local procedure)
#       LIT 0, 3
#       OPR 0, 14
#       OPR 0, 0
#   Z0: CAL ?, ?
#       CAL ?, ?
#
# We must know that when compiling A1 we have no info on the location of A2.
# The compilation of A1 yields two placeholder CALs: one at B1 for function
# A2, one at B2 for function B1. Since B1 is local we are able to get its
# location, but we can't say the same thing about A2.
# From this we can refine the list of things to do when compiling a block:
# 1.  Collect all constant definitions.
# 2.  Allocate variables.
# 3.  Compile all local procedures.
# 4.  Record the locations of local procedures.
# 5.  Resolve placeholder CALs only for the call to the local procedures
#     recorded in step 4. The rest would have to be resolved when compiling
#     for outer layers. The depth is maintained by increasing by one with
#     each ascension of layers.
# 6.  Compile block body.
# This process would still generate a list of placeholder CALs that are not
# resolved; thus the return type of this function still has a seq[(int, int, string)].
# Compiling a proc is mostly the same as compiling a block, the difference
# being that when compiling a proc the name of the proc is added to the
# environment to enable recursion. The name of the proc, when resolving, has
# a depth of 1 (instead of 0 like calling local procedures) since technically
# lives in the parent scope.
proc compileBlock(x: Block, currentLoc: int, env: var Env, argTable: TableRef[string, int]): (seq[Instr], seq[(int, int, string)])
proc compileProcDef(x: ProcDef, currentLoc: int, env: var Env): (seq[Instr], seq[(int, int, string)]) =
  let argTable = x.assignParams()
  let res = x.body.compileBlock(currentLoc, env, argTable)
  var resInstrList = res[0]
  var newCallFillers: seq[(int, int, string)] = @[]
  for c in res[1]:
    let calLoc = c[0]
    let calName = c[2]
    if calName == x.name:
      resInstrList[calLoc-currentLoc] = (CAL, currentLoc)
    else:
      newCallFillers.add((c[0], c[1]+1, c[2]))
  resInstrList.add((OPR, 0))
  return (resInstrList, newCallFillers)

proc compileBlock(x: Block, currentLoc: int, env: var Env, argTable: TableRef[string, int]): (seq[Instr], seq[(int, int, string)]) =
  # echo "compiling ", name, " at loc ", currentLoc, " at layer ", layerCount
  var blockBase = currentLoc
  let constTable = if x.constDef.len <= 0: nil else: x.constDef.collectConst
  var res: seq[Instr] = @[]
  var callFillers: seq[(int, int, string)] = @[]
  var procTable: TableRef[string, tuple[loc: int, arity: int]] = newTable[string, tuple[loc: int, arity: int]]()
  var varTable: TableRef[string, int] = nil
  if x.varDef.len > 0:
    res.add((INT, x.varDef.len))
    varTable = x.varDef.allocVar()
    blockBase += 1
  var globalTable: TableRef[string, int] = nil
  let newEnvFrame = (constTable: constTable,
                     globalTable: globalTable,
                     varTable: varTable,
                     procTable: procTable,
                     argTable: argTable)
  env.add(newEnvFrame)

  let bodyRes = x.body.compileStatement(blockBase, env)
  discard env.pop()
  res &= bodyRes[0]
  let bodyCallFillers = bodyRes[1]
  for c in bodyCallFillers:
    let calLoc = c[0]
    let calName = c[2]
    if procTable.hasKey(calName):
      res[calLoc-currentLoc] = (CAL, procTable[calName].loc)
    else:
      callFillers.add((c[0], c[1], c[2]))
  return (res, callFillers)
proc compileBlock(x: Block, currentLoc: int, env: var Env): (seq[Instr], seq[(int, int, string)]) =
  compileBlock(x, currentLoc, env, nil)

proc compileProgram*(x: Program): seq[Instr] =
  # echo "compiling ", name, " at loc ", currentLoc, " at layer ", layerCount
  var blockBase = 0
  let constTable = if x.constDef.len <= 0: nil else: x.constDef.collectConst
  var res: seq[Instr] = @[]
  var callFillers: seq[(int, int, string)] = @[]
  var procTable: TableRef[string, tuple[loc: int, arity: int]] = newTable[string, tuple[loc: int, arity: int]]()
  var varTable: TableRef[string, int] = nil
  var globalTable: TableRef[string, int] = nil
  if x.varDef.len > 0:
    res.add((INT, x.varDef.len))
    globalTable = x.varDef.allocVar()
    blockBase += 1
  var argTable: TableRef[string, int] = nil
  let newEnvFrame = (constTable: constTable,
                     globalTable: globalTable,
                     varTable: varTable,
                     procTable: procTable,
                     argTable: argTable)
  var env = @[newEnvFrame]

  if x.procDef.len > 0:
    # NOTE: we can resolve this locally because we can calculate the sizes of
    # local procedures locally. This is a placeholder that we'll resolve later.
    res.add((JMP, 0))
    blockBase += 1
    var procLocationCount = blockBase
    # NOTE: here we collect arity information & use it to check CALL statements;
    # this info is used to check local procedures (to support mutual recursion)
    # and the body *only*; remember that we only resolve procedure addr *after*
    # everything is compiled. The `loc` here is not used in compileStatement;
    # it's only some dummy value for now.
    for p in x.procDef:
      procTable[p.name] = (loc: procLocationCount, arity: p.paramList.len)
    let layerCount = 0
    for p in x.procDef:
      let pRes = p.compileProcDef(procLocationCount, env)
      # NOTE: we need to update procTable again because the last time we update
      # this we updated it with dummy values; this time we need to insert all
      # the correct values.
      procTable[p.name] = (loc: procLocationCount, arity: p.paramList.len)
      res &= pRes[0]
      callFillers &= pRes[1]
      procLocationCount += pRes[0].len
    # NOTE: since the whole proc starts at currentLoc, one can find the
    # relative location of the CALs by i-currentLoc.
    var newCallFillers: seq[(int, int, string)] = @[]
    for c in callFillers:
      let calLoc = c[0]
      let calName = c[2]
      if procTable.hasKey(calName):
        res[calLoc] = (CAL, procTable[calName].loc)
      else:
        newCallFillers.add((c[0], c[1], c[2]))
    callFillers = newCallFillers
    # resolving the JMP we setup in the beginning...
    res[blockBase-1] = (JMP, procLocationCount)
    blockBase = procLocationCount

  let bodyRes = x.body.compileStatement(blockBase, env)
  discard env.pop()
  res &= bodyRes[0]
  let bodyCallFillers = bodyRes[1]
  for c in bodyCallFillers:
    let calLoc = c[0]
    let calName = c[2]
    if procTable.hasKey(calName):
      res[calLoc] = (CAL, procTable[calName].loc)
    else:
      callFillers.add((c[0], c[1]+1, c[2]))

  assert callfillers.len <= 0
  return res
  

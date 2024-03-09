import std/options
from std/strformat import `&`
from std/strutils import parseInt
import ast
import prettyprint
from std/sequtils import foldr

type
  ParserState = ref object
    line: int
    col: int
    x: string
    stp: int

let reservedWords: seq[string] = @[
  "if", "then", "while", "do", "begin", "end", "procedure", "const", "var", "input", "print", "return", "valof", "ref", "elif", "else"
]

proc raiseErrorWithReason(x: ParserState, reason: string): void =
  raise newException(ValueError, &"[Parser] ({x.line+1},{x.col+1}) {reason}")

proc ended(x: ParserState): bool {.inline.} =
  x.stp >= x.x.len

proc isDigit(x: char): bool {.inline.} =
  '0' <= x and x <= '9'
proc isNameHeadChar(x: char): bool {.inline.} =
  ('a' <= x and x <= 'z') or ('A' <= x and x <= 'Z') or x == '_'
proc isNameChar(x: char): bool {.inline.} =
  x.isDigit or x.isNameHeadChar

proc takeIdent(x: ParserState): Option[string] =
  var i = x.stp
  let lenx = x.x.len
  if i < lenx and x.x[i].isNameHeadChar: i += 1
  else: return none(string)
  while i < lenx and x.x[i].isNameChar: i += 1
  let name = x.x[x.stp..<i]
  if name in reservedWords: return none(string)
  x.col += i-x.stp
  x.stp = i
  return some(name)

proc takeInteger(x: ParserState): Option[int] =
  var i = x.stp
  let lenx = x.x.len
  if i < lenx and x.x[i].isDigit: i += 1
  else: return none(int)
  while i < lenx and x.x[i].isDigit: i += 1
  let name = x.x[x.stp..<i]
  x.col += i-x.stp
  x.stp = i
  return some(name.parseInt)

proc expect(x: ParserState, pat: string): Option[string] =
  let lenx = x.x.len
  if lenx-x.stp < pat.len: return none(string)
  let prefix = x.x[x.stp..<x.stp+pat.len]
  if prefix != pat: return none(string)
  for i in pat:
    if i in "\n\v\f":
      x.line += 1
      x.col = 0
    else:
      x.col += 1
  x.stp += pat.len
  return some(pat)

proc peek(x: ParserState, pat: string): bool = 
  let lenx = x.x.len
  if lenx-x.stp < pat.len: return false
  let prefix = x.x[x.stp..<x.stp+pat.len]
  if prefix != pat: return false
  return true

proc peekFullWord(x: ParserState, pat: string): bool =
  let lenx = x.x.len
  if lenx-x.stp < pat.len: return false
  let prefix = x.x[x.stp..<x.stp+pat.len]
  if prefix != pat: return false
  if x.stp+pat.len < lenx and x.x[x.stp+pat.len].isNameChar: return false
  return true
  
proc skipWhiteOnly(x: ParserState): ParserState =
  var i = x.stp
  let lenx = x.x.len
  while i < lenx and x.x[i] in " \n\r\v\t\b\f":
    if x.x[i] in "\n\v\f":
      x.line += 1
      x.col = 0
    else:
      x.col += 1
    i += 1
  x.stp = i
  return x
# NOTE: I would say this could be quite slow but does the job.
proc skipComment(x: ParserState): ParserState =
  discard x.skipWhiteOnly
  if not x.peek("(*"): return x
  discard x.expect("(*")
  var cnt = 0
  let lenx = x.x.len
  while not x.ended and cnt >= 0:
    if x.peek("(*"):
      cnt += 1
      x.stp += 2
      x.col += 2
    elif x.peek("*)"):
      cnt -= 1
      x.stp += 2
      x.col += 2
    else:
      if x.x[x.stp] in "\n\v\f":
        x.line += 1
        x.col = 0
      else:
        x.col += 1
      x.stp += 1
  # NOTE: we disregard the case where the source code ends before the
  # comment does; we just treat it as if the comment ends as well.
  return x
    
proc skipWhite(x: ParserState): ParserState =
  var lastStp = x.stp
  while not x.ended:
    discard x.skipWhiteOnly
    discard x.skipComment
    if x.stp == lastStp: break
    lastStp = x.stp
  return x

proc parseExpr(x: ParserState): Option[Expr]
proc parseRefterm(x: ParserState): Option[Expr] =
  discard x.skipWhite();
  var
    line = x.line
    col = x.col
  if x.skipWhite().peekFullWord("ref"):
    discard x.skipWhite().expect("ref")
    discard x.skipWhite()
    var
      idline = x.line
      idcol = x.col
    let z1 = x.skipWhite().takeIdent()
    if z1.isNone(): x.raiseErrorWithReason("Identifier expected.")
    return some(Expr(line: line, col: col, eType: E_UNARYOP, uOp: "ref", uBody: Expr(line: idline, col: idcol, eType: E_VAR, vName: z1.get())))
  
  let z1 = x.skipWhite().takeIdent()
  if z1.isSome(): return some(Expr(line: line, col: col, eType: E_VAR, vName: z1.get()))
  let z2 = x.skipWhite().takeInteger()
  if z2.isSome(): return some(Expr(line: line, col: col, eType: E_LIT, lVal: z2.get()))
  if x.skipWhite.expect("(").isNone(): return none(Expr)
  let z3 = x.skipWhite.parseExpr()
  if z3.isNone(): x.raiseErrorWithReason("Expression expected.")
  if x.skipWhite.expect(")").isNone(): x.raiseErrorWithReason("Right parenthesis expected.")
  return z3

proc parseFactor(x: ParserState): Option[Expr] =
  discard x.skipWhite()
  var linecolList: seq[(int, int)] = @[]
  var derefCount = 0
  while x.peek("valof"):
    linecolList.add((x.line, x.col))
    discard x.expect("valof")
    discard x.skipWhite()
    derefCount += 1
  let
    bodyLine = x.line
    bodyCol = x.col
  let body = x.skipWhite.parseRefterm
  if derefCount <= 0 and body.isNone(): return none(Expr)
  if derefCount > 0 and body.isNone(): x.raiseErrorWithReason("Expression expected.")
  var subj = body.get()
  var i = 0
  while i < derefCount:
    let lc = linecolList[derefCount-i-1]
    subj = Expr(line: lc[0], col: lc[1], eType: E_UNARYOP, uOp: "valof", uBody: subj)
    i += 1
  return some(subj)

proc parseTerm(x: ParserState): Option[Expr] =
  discard x.skipWhite
  let line = x.line
  let col = x.col
  var res = x.skipWhite.parseFactor
  if res.isNone(): return none(Expr)
  while true:
    var thisOp = x.skipWhite.expect("*")
    if thisOp.isNone(): thisOp = x.skipWhite.expect("/")
    if thisOp.isNone(): thisOp = x.skipWhite.expect("%")
    if thisOp.isNone(): return res
    var rhs = x.skipWhite.parseFactor
    if rhs.isNone(): x.raiseErrorWithReason("Term expected.")
    res = some(Expr(line: line, col: col, eType: E_BINOP, binop: thisOp.get(), bLhs: res.get(), bRhs: rhs.get()))
    continue

proc parseExpr(x: ParserState): Option[Expr] =
  discard x.skipWhite
  let line = x.line
  let col = x.col
  var prefixUnaryOp = x.skipWhite.expect("+")
  if prefixUnaryOp.isNone(): prefixUnaryOp = x.skipWhite.expect("-")
  var res = x.skipWhite.parseTerm
  if res.isNone():
    if prefixUnaryOp.isNone(): return none(Expr)
    else: x.raiseErrorWithReason("Term expected.")
  if prefixUnaryOp.isSome():
    res = some(Expr(line: line, col: col, eType: E_UNARYOP, uOp: prefixUnaryOp.get(), uBody: res.get()))
  while true:
    var thisOp = x.skipWhite.expect("+")
    if thisOp.isNone(): thisOp = x.skipWhite.expect("-")
    if thisOp.isNone(): return res
    var rhs = x.skipWhite.parseTerm
    if rhs.isNone(): x.raiseErrorWithReason("Term expected.")
    res = some(Expr(line: line, col: col, eType: E_BINOP, binop: thisOp.get(), bLhs: res.get(), bRhs: rhs.get()))
    continue

# Cond ::= Cond1 {"or" Cond1}
# Cond1 ::= Cond2 {"and" Cond2}
# Cond2 ::= "odd" Expr
#         | Expr ("="|"!="|"<="|"<"|">="|">") Expr
#         | "not" Cond
#         | "(" Cond ")"
proc parseCond(x: ParserState): Option[Cond]
proc parseCond2(x: ParserState): Option[Cond] =
  var line = x.line
  var col = x.col
  var shouldBePred = x.skipWhite.expect("odd")
  if shouldBePred.isSome():
    var body = x.skipWhite.parseExpr
    if body.isNone(): x.raiseErrorWithReason("Expression expected.")
    return some(Cond(line: line, col: col, cType: C_EXPR_PRED, predName: shouldBePred.get(), pBody: body.get()))
  let shouldBeNot = x.skipWhite.expect("not")
  if shouldBeNot.isSome():
    var body = x.skipWhite.parseCond
    if body.isNone(): x.raiseErrorWithReason("Condition expected.")
    return some(Cond(line: line, col: col, cType: C_EXPR_NOT, nBody: body.get))
  let leftParen = x.skipWhite.expect("(")
  if leftParen.isSome():
    var body = x.skipWhite.parseCond
    if body.isNone(): x.raiseErrorWithReason("Condition expected.")
    if x.skipWhite.expect(")").isNone(): x.raiseErrorWithReason("Right parenthesis expected.")
    return body
  var lhs = x.skipWhite.parseExpr
  if lhs.isNone(): return none(Cond)
  var thisOp = x.skipWhite.expect("=")
  if thisOp.isNone(): thisOp = x.skipWhite.expect("!=")
  if thisOp.isNone(): thisOp = x.skipWhite.expect("<=")
  if thisOp.isNone(): thisOp = x.skipWhite.expect("<")
  if thisOp.isNone(): thisOp = x.skipWhite.expect(">=")
  if thisOp.isNone(): thisOp = x.skipWhite.expect(">")
  if thisOp.isNone(): x.raiseErrorWithReason("Expression expected.")
  var rhs = x.skipWhite.parseExpr
  if rhs.isNone(): x.raiseErrorWithReason("Expression expected.")
  return some(Cond(line: line, col: col, cType: C_EXPR_REL, relOp: thisOp.get(), relLhs: lhs.get(), relRhs: rhs.get()))
proc parseCond1(x: ParserState): Option[Cond] =
  let line = x.line
  let col = x.col
  let lhs = x.skipWhite.parseCond2
  if lhs.isNone(): return none(Cond)
  if not x.skipWhite.peek("and"): return lhs
  var subjList: seq[Cond] = @[lhs.get]
  while x.skipWhite.peek("and"):
    discard x.skipWhite.expect("and")
    let next = x.skipWhite.parseCond2
    if next.isNone(): x.raiseErrorWithReason("Condition expected.")
    subjList.add(next.get())
  return some(foldr(subjList, Cond(line: a.line, col: a.col,
                                   cType: C_EXPR_BINOP,
                                   binOp: "and",
                                   binLhs: a,
                                   binRhs: b)))
proc parseCond(x: ParserState): Option[Cond] =
  let line = x.line
  let col = x.col
  let lhs = x.skipWhite.parseCond1
  if lhs.isNone(): return none(Cond)
  if not x.skipWhite.peek("or"): return lhs
  var subjList: seq[Cond] = @[lhs.get]
  while x.skipWhite.peek("or"):
    discard x.skipWhite.expect("or")
    let next = x.skipWhite.parseCond1
    if next.isNone(): x.raiseErrorWithReason("Condition expected.")
    subjList.add(next.get())
  return some(foldr(subjList, Cond(line: a.line, col: a.col,
                                   cType: C_EXPR_BINOP,
                                   binOp: "or",
                                   binLhs: a,
                                   binRhs: b)))
  
proc parseLValue(x: ParserState): Option[LValue] =
  discard x.skipWhite
  let line = x.line
  let col = x.col
  var possibleDereferrencedTarget = x.skipWhite.parseExpr()
  if possibleDereferrencedTarget.isNone(): return none(LValue)
  if x.peek("[]"):
    var derefCount = 1
    discard x.expect("[]")
    while x.peek("[]"):
      discard x.expect("[]") 
      derefCount += 1
    var subj = possibleDereferrencedTarget.get()
    var i = 0
    while i < derefCount:
      subj = Expr(line: line, col: col, eType: E_UNARYOP, uOp: "valof", uBody: subj)
      i += 1
    return some(LValue(line: line, col: col, lvType: LV_DEREF, drBody: subj))
  else:
    assert(possibleDereferrencedTarget.get().eType == E_VAR)
    var name = possibleDereferrencedTarget.get().vName
    return some(LValue(line: line, col: col, lvType: LV_VAR, vName: name))

proc parseStatement(x: ParserState): Option[Statement] =
  discard x.skipWhite
  let line = x.line
  let col = x.col
  if x.skipWhite.peek("call"):
    discard x.skipWhite.expect("call")
    var target = x.skipWhite.takeIdent()
    if target.isNone(): x.raiseErrorWithReason("Identifier expected.")
    var argList: seq[Expr] = @[]
    if x.skipWhite.peek("("):
      discard x.skipWhite.expect("(")
      if x.skipWhite.peek(")"):
        discard x.skipWhite.expect(")")
      else:
        let expr = x.skipWhite.parseExpr()
        if expr.isNone(): x.raiseErrorWithReason("Expression or right parenthesis expected.")
        argList.add(expr.get())
        while not x.skipWhite.peek(")"):
          var sep = x.skipWhite.expect(",")
          if sep.isNone(): x.raiseErrorWithReason("Comma or right parenthesis expected.")
          var nextExpr = x.skipWhite.parseExpr
          if nextExpr.isNone(): x.raiseErrorWithReason("Expression expected.")
          argList.add(nextExpr.get())
        if x.skipWhite.expect(")").isNone(): x.raiseErrorWithReason("Right parenthesis expected.")
    return some(Statement(line: line, col: col, sType: S_CALL, cTarget: target.get(), cArgs: argList))
  if x.skipWhite.peek("input"):
    discard x.skipWhite.expect("input")
    var target = x.skipWhite.parseLValue()
    if target.isNone(): x.raiseErrorWithReason("Proper lvalue expected.")
    return some(Statement(line: line, col: col, sType: S_INPUT, iTarget: target.get()))
  if x.skipWhite.peek("print"):
    discard x.skipWhite.expect("print")
    var exprList: seq[Expr] = @[]
    var target = x.skipWhite.parseExpr()
    if target.isNone(): x.raiseErrorWithReason("Expression expected.")
    exprList.add(target.get)
    while x.skipWhite.peek(","):
      discard x.skipWhite.expect(",")
      var target = x.skipWhite.parseExpr()
      if target.isNone(): break
      exprList.add(target.get)
    return some(Statement(line: line, col: col, sType: S_PRINT, pExpr: exprList))
  if x.skipWhite.peek("begin"):
    discard x.skipWhite.expect("begin")
    var body: seq[Statement] = @[]
    var thisStmt = x.skipWhite.parseStatement
    if thisStmt.isNone(): x.raiseErrorWithReason("Statement expected.")
    body.add(thisStmt.get())
    # NOTE: this is slightly different from the original PL/0: here we allow
    # empty statements too.
    while not x.skipWhite.peek("end"):
      if x.skipWhite.peek(";"):
        discard x.skipWhite.expect(";")
        continue
      var nextStatement = x.skipWhite.parseStatement
      if nextStatement.isNone(): x.raiseErrorWithReason("Statement expected.")
      body.add(nextStatement.get())
    if x.skipWhite.expect("end").isNone(): x.raiseErrorWithReason("\"end\" expected.")
    return some(Statement(line: line, col: col, sType: S_BLOCK, body: body))
  if x.skipWhite.peek("if"):
    discard x.skipWhite.expect("if")
    var cond = x.skipWhite.parseCond
    if cond.isNone(): x.raiseErrorWithReason("Condition expected.")
    if x.skipWhite.expect("then").isNone(): x.raiseErrorWithReason("\"then\" expected.")
    var body = x.skipWhite.parseStatement
    if body.isNone(): x.raiseErrorWithReason("Statement expected.")
    var branchList: seq[(Cond, Statement)] = @[(cond.get, body.get)]
    var elseBranch: Statement = nil
    while true:
      if x.skipWhite.peek("elif"):
        discard x.skipWhite.expect("elif")
        cond = x.skipWhite.parseCond
        if cond.isNone(): x.raiseErrorWithReason("Condition expected.")
        if x.skipWhite.expect("then").isNone(): x.raiseErrorWithReason("\"then\" expected.")
        body = x.skipWhite.parseStatement
        if body.isNone(): x.raiseErrorWithReason("Statement expected.")
        branchList.add((cond.get, body.get))
      elif x.skipWhite.peek("else"):
        discard x.skipWhite.expect("else")
        body = x.skipWhite.parseStatement
        if body.isNone(): x.raiseErrorWithReason("Statement expected.")
        elseBranch = body.get
        break
      else:
        break
    return some(Statement(line: line, col: col, sType: S_IF,
                          branchList: branchList,
                          elseBranch: elseBranch))
  if x.skipWhite.peek("while"):
    discard x.skipWhite.expect("while")
    var cond = x.skipWhite.parseCond
    if cond.isNone(): x.raiseErrorWithReason("Condition expected.")
    if x.skipWhite.expect("do").isNone(): x.raiseErrorWithReason("\"do\" expected.")
    var body = x.skipWhite.parseStatement
    if body.isNone(): x.raiseErrorWithReason("Statement expected.")
    return some(Statement(line: line, col: col, sType: S_WHILE, wCond: cond.get(), wBody: body.get()))
  if x.skipWhite.peek("return"):
    discard x.skipWhite.expect("return")
    var expr = x.skipWhite.parseExpr
    if expr.isNone(): x.raiseErrorWithReason("Expression expected.")
    return some(Statement(line: line, col: col, sType: S_RETURN, rExpr: expr.get()))
  var ident = x.skipWhite.parseLValue()
  if ident.isNone(): x.raiseErrorWithReason("Proper lvalue (or any of the statement keyword) expected.")
  if x.skipWhite.expect(":=").isNone(): x.raiseErrorWithReason("\":=\" expected.")
  var rhs = x.skipWhite.parseExpr
  if rhs.isNone(): x.raiseErrorWithReason("Expression expected.")
  return some(Statement(line: line, col: col, sType: S_ASSIGN, aTarget: ident.get(), aVal: rhs.get()))

proc parseConstClause(x: ParserState): Option[seq[(string, int)]] =
  if x.expect("const").isNone(): return none(seq[(string, int)])
  var firstIdent = x.skipWhite.takeIdent
  if firstIdent.isNone(): x.raiseErrorWithReason("Identifier expected.")
  if x.skipWhite.expect("=").isNone(): x.raiseErrorWithReason("\"=\" expected.")
  var firstNumber = x.skipWhite.takeInteger
  if firstNumber.isNone(): x.raiseErrorWithReason("Integer expected.")
  var res: seq[(string, int)] = @[(firstIdent.get(), firstNumber.get())]
  while true:
    if x.skipWhite.expect(",").isNone(): break
    var ident = x.skipWhite.takeIdent
    if ident.isNone(): x.raiseErrorWithReason("Identifier expected.")
    if x.skipWhite.expect("=").isNone(): x.raiseErrorWithReason("\"=\" expected.")
    var number = x.skipWhite.takeInteger
    if number.isNone(): x.raiseErrorWithReason("Integer expected.")
    res.add((ident.get(), number.get()))
  if x.skipWhite.expect(";").isNone(): x.raiseErrorWithReason("\";\" expected.")
  return some(res)

proc parseVarClause(x: ParserState): Option[seq[string]] =
  if x.skipWhite.expect("var").isNone(): return none(seq[string])
  var firstIdent = x.skipWhite.takeIdent
  if firstIdent.isNone(): x.raiseErrorWithReason("Identifier expected.")
  var res: seq[string] = @[firstIdent.get()]
  while true:
    if x.skipWhite.expect(",").isNone(): break
    var ident = x.skipWhite.takeIdent
    if ident.isNone(): x.raiseErrorWithReason("Identifier expected.")
    res.add(ident.get())
  if x.skipWhite.expect(";").isNone(): x.raiseErrorWithReason("\";\" expected.")
  return some(res)

proc parseBlock(x: ParserState): Option[Block]
proc parseProcClause(x: ParserState): Option[seq[ProcDef]] =
  var res: seq[ProcDef] = @[]
  while true:
    discard x.skipWhite
    let line = x.line
    let col = x.col
    if x.skipWhite.expect("procedure").isNone(): break
    var ident = x.skipWhite.takeIdent
    if ident.isNone(): x.raiseErrorWithReason("Identifier expected.")
    var paramList: seq[string] = @[]
    if x.skipWhite.peek("("):
      discard x.skipWhite.expect("(")
      if x.skipWhite.peek(")"):
        discard x.skipWhite.expect(")")
      else:
        let firstIdent = x.skipWhite.takeIdent()
        if firstIdent.isNone(): x.raiseErrorWithReason("Identifier expected.")
        paramList.add(firstIdent.get())
        while not x.skipWhite.peek(")"):
          if not x.skipWhite.peek(","): x.raiseErrorWithReason("Comma or right parenthesis expected.")
          discard x.skipWhite.expect(",")
          let ident = x.skipWhite.takeIdent()
          if ident.isNone(): x.raiseErrorWithReason("Identifier expected.")
          paramList.add(ident.get())
        if x.skipWhite.expect(")").isNone(): x.raiseErrorWithReason("Right parenthesis expected.")
    if x.skipWhite.expect(";").isNone(): x.raiseErrorWithReason("\";\" expected.")
    var blockRes = x.skipWhite.parseBlock
    if blockRes.isNone(): x.raiseErrorWithReason("Block expected.")
    if x.skipWhite.expect(";").isNone(): x.raiseErrorWithReason("\";\" expected.")
    for v in blockRes.get().varDef:
      if v in paramList: x.raiseErrorWithReason("Variable {v} is already defined as parameter.")
    res.add(ProcDef(line: line, col: col, name: ident.get(), paramList: paramList, body: blockRes.get()))
  return some(res)
  
proc parseBlock(x: ParserState): Option[Block] =
  discard x.skipWhite
  let line = x.line
  let col = x.col
  var constClause = x.skipWhite.parseConstClause
  var varClause = x.skipWhite.parseVarClause
  var body = x.skipWhite.parseStatement
  if body.isNone(): x.raiseErrorWithReason("Statement expected.")
  return some(Block(line: line, col: col,
                    constDef: if constClause.isNone(): @[] else: constClause.get(),
                    varDef: if varClause.isNone(): @[] else: varClause.get(),
                    body: body.get()))

proc parseProgram(x: ParserState): Option[Program] =
  var constClause = x.skipWhite.parseConstClause
  var varClause = x.skipWhite.parseVarClause
  var procClause = x.skipWhite.parseProcClause
  var body = x.skipWhite.parseStatement
  if body.isNone(): x.raiseErrorWithReason("Statement expected.")
  return some(Program(constDef: if constClause.isNone(): @[] else: constClause.get(),
                      varDef: if varClause.isNone(): @[] else: varClause.get(),
                      procDef: if procClause.isNone(): @[] else: procClause.get(),
                      body: body.get()))

proc parseProgram*(x: string): Option[Program] =
  ParserState(line: 0, col: 0, x: x, stp: 0).parseProgram

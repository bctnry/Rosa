from std/strutils import parseInt
from std/strformat import `&`

type
  InstrType* = enum
    LIT
    OPR
    LOD
    STO
    CAL
    INT
    JMP
    JPC
    POP
    POPA
    PUSHA
    REF
    DEREF
    POPR
  Instr* = (InstrType, int, int)

proc `$`*(x: InstrType): string =
  case x:
    of LIT: "LIT"
    of OPR: "OPR"
    of LOD: "LOD"
    of STO: "STO"
    of CAL: "CAL"
    of INT: "INT"
    of JMP: "JMP"
    of JPC: "JPC"
    of POP: "POP"
    of POPA: "POPA"
    of PUSHA: "PUSHA"
    of REF: "REF"
    of DEREF: "DEREF"
    of POPR: "POPR"

type
  VM* = ref object
    pc*: int
    base*: int
    stk*: int
    stkmem*: array[2048,int]
    program*: seq[Instr]
    a*: int

proc loadVM*(program: seq[Instr]): VM =
  VM(pc: 0,
     base: 1,
     stk: 0,
     program: program,
     a: 0)
    
proc runVM*(vm: VM): void =
  # NOTE: this traces the static link)
  proc traceStaticLink(vm: VM, currentBase: int, layerCount: int): int =
    var subj = currentBase
    var lc = layerCount
    while lc > 0:
      subj = vm.stkmem[subj]
      lc -= 1
    return subj
    
  while vm.pc < vm.program.len:
    let i = vm.program[vm.pc]
    let iType = i[0]
    let iLayer = i[1]
    let iArg = i[2]
    case iType:
      of LIT:
        vm.stk += 1
        vm.stkmem[vm.stk] = iArg
        vm.pc += 1
      of OPR:
        case iArg:
          of 0:  # return
            # prev. stktop
            # static link
            # dynamic link
            # retaddr
            vm.stk = vm.base-1
            vm.pc = vm.stkmem[vm.stk+3]
            vm.base = vm.stkmem[vm.stk+2]
          of 1:
            vm.stkmem[vm.stk] = -vm.stkmem[vm.stk]
            vm.pc += 1
          of 2:
            vm.stk -= 1
            vm.stkmem[vm.stk] += vm.stkmem[vm.stk+1]
            vm.pc += 1
          of 3:
            vm.stk -= 1
            vm.stkmem[vm.stk] -= vm.stkmem[vm.stk+1]
            vm.pc += 1
          of 4:
            vm.stk -= 1
            vm.stkmem[vm.stk] *= vm.stkmem[vm.stk+1]
            vm.pc += 1
          of 5:
            vm.stk -= 1
            vm.stkmem[vm.stk] = vm.stkmem[vm.stk] div vm.stkmem[vm.stk+1]
            vm.pc += 1
          of 6:
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] mod 2 == 1: 1 else: 0
            vm.pc += 1
          of 7:  # input
            stdout.write("? "); stdout.flushFile()
            let z = stdin.readLine().parseInt
            vm.stk += 1
            vm.stkmem[vm.stk] = z
            vm.pc += 1
          of 8:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] == vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 9:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] != vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 10:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] < vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 11:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] <= vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 12:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] > vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 13:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] >= vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 14:  # print
            echo vm.stkmem[vm.stk]
            vm.stk -= 1
            vm.pc += 1
          of 15:  # halt
            break
          else:
            raise newException(ValueError, &"[VM] Unsupported OPR function: {iArg}")
      of LOD:
        vm.stk += 1
        vm.stkmem[vm.stk] = vm.stkmem[vm.traceStaticLink(vm.base, iLayer) + iArg]
        vm.pc += 1
      of STO:
        vm.stkmem[vm.traceStaticLink(vm.base, iLayer) + iArg] = vm.stkmem[vm.stk]
        vm.stk -= 1
        vm.pc += 1
      of CAL:
        vm.stkmem[vm.stk+1] = vm.traceStaticLink(vm.base, iLayer)
        vm.stkmem[vm.stk+2] = vm.base
        vm.stkmem[vm.stk+3] = vm.pc+1
        vm.base = vm.stk+1
        vm.pc = iArg
        vm.stk = vm.stk+3
      of INT:
        vm.stk += iArg
        vm.pc += 1
      of JMP:
        vm.pc = iArg
      of JPC:
        if vm.stkmem[vm.stk] == 0:
          vm.pc = iArg
          vm.stk -= 1
        else:
          vm.pc += 1
      of POP:
        vm.stk -= 1
        vm.pc += 1
      of PUSHA:
        vm.stk += 1
        vm.stkmem[vm.stk] = vm.a
      of POPA:
        vm.a = vm.stkmem[vm.stk]
        vm.stk -= 1
        vm.pc += 1
      of REF:
        vm.stk += 1
        vm.stkmem[vm.stk] = vm.traceStaticLink(vm.base, iLayer) + iArg
        vm.pc += 1
      of DEREF:
        vm.stkmem[vm.stk] = vm.stkmem[vm.stkmem[vm.stk]]
        vm.pc += 1
      of POPR:
        vm.stkmem[vm.a] = vm.stkmem[vm.stk]
        vm.stk -= 1
        vm.pc += 1

# NOTE THAT in the definition of JPC we jump when the stacktop is *0* but the
# comparison operators leave *1* at the stack top when the conditio holds;
# this is differnt from what we are used to but I believe this has a very
# simple reason. Consider this example:
# 
#   if a > 3 then
#   begin
#     a := 3;
#   end;
#
# If JPC jumps when stacktop is 1 then the compiled code should be:
#
#       LOD (a)
#       LIT 0, 3
#       OPR 0, 12
#       JPC 0, L1
#       JMP 0, L2
#   L1: LIT 0, 3
#       STO (a)
#   L2:
#
# But if JPC jumps when stacktop is 0 then the compiled code should be:
#
#       LOD (a)
#       LIT 0, 3
#       OPR 0, 12
#       JPC 0, L1
#       LIT 0, 3
#       STO (a)
#   L1:
#
# Which is one instruction less; this design desicion would have the same
# effect on compiling WHILE.

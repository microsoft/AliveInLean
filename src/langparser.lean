import .lang
import .lang_tostr
import data.buffer.parser

open parser

-- ReadLinebreaks reads zero or more '\n's.
def ReadLinebreaks: parser unit :=
  many' (ch '\n')

-- ReadLine reads a line.
def ReadLine: parser string :=
  many_char1 $ sat $ λ c, c ≠ '\n'

-- ReadWhitespaces reads zero or more whitespaces.
def ReadWhitespaces: parser unit :=
  decorate_error "Whitespace expected" $ many' $ sat $ λ c, c.is_whitespace

-- Reads a register.
def ReadReg: parser reg :=
  do
  ch '%',
  cs ← many_char1 $ sat $ λ c, c.is_alpha ∨ c.is_digit ∨ c = '_' ∨ c = '.',
  return (reg.r ("%" ++ cs))

-- Reads one constant.
-- Only positive number is supported currently.
def ReadIntConst: parser const :=
  do
  is_neg ← ((do ch '-', return tt) <|> return ff),
  cs ← many_char1 $ sat $ λ c, c.is_digit,
  -- coercion from nat to int
  return (const.int (if is_neg then -1 * (cs.to_nat) else cs.to_nat))

-- Reads a value.
-- Either ReadReg or ReadConst.
def ReadVal: parser operand :=
  (do r ← ReadReg, return (operand.reg r)) <|>
  (do str "true", return (operand.const (const.int (-1)))) <|>
  (do str "false", return (operand.const (const.int 0))) <|>
  (do c ← ReadIntConst, return (operand.const c)) <|>
  failure

def ReadBinaryInstFlag: parser bopflag :=
  (do str "nsw", ReadWhitespaces, return bopflag.nsw) <|>
  (do str "nuw", ReadWhitespaces, return bopflag.nuw) <|>
  (do str "exact", ReadWhitespaces, return bopflag.exact)

def ReadType: parser ty :=
  do
  ch 'i',
  sz ← many_char1 $ sat $ λ c, c.is_digit,
  return (ty.int sz.to_nat)

-- Reads a binary instruction.
def ReadBinaryInst (lhs:reg) (opname:string) (bopc:bopcode) : parser instruction :=
  do
  str opname,
  ReadWhitespaces,
  flags ← many ReadBinaryInstFlag,
  ReadWhitespaces,
  retty ← (ReadType <|> return (ty.arbitrary_int)),
  ReadWhitespaces,
  v1 ← ReadVal,
  ReadWhitespaces,
  ch ',',
  ReadWhitespaces,
  v2 ← ReadVal,
  ReadWhitespaces,
  ReadLinebreaks,
  return (instruction.binop retty lhs bopc flags v1 v2)

-- Reads "cast" instructions.
def ReadCastInst (lhs:reg) (opname:string) (uopc:uopcode): parser instruction :=
  do
  str opname,
  ReadWhitespaces,
  fromty ← (ReadType <|> return (ty.arbitrary_int)),
  ReadWhitespaces,
  v ← ReadVal,
  ReadWhitespaces,
  str "to",
  ReadWhitespaces,
  toty ← ReadType,
  ReadLinebreaks,
  return (instruction.unaryop lhs uopc fromty v toty)

def ReadICmpCond: parser icmpcond :=
  let ls := [icmpcond.eq, icmpcond.ne, icmpcond.ugt, icmpcond.uge,
              icmpcond.ult, icmpcond.ule, icmpcond.sgt, icmpcond.sge,
              icmpcond.slt, icmpcond.sle] in
  let fs := ls.map (λ (cond:icmpcond), do str (to_string cond), return cond) in
  list.foldl (λ a b, a <|> b) fs.head fs.tail

-- Reads "icmp" instruction.
def ReadSelectInst (lhs:reg): parser instruction :=
  do
  str "select",
  ReadWhitespaces,
  condty ← (ReadType <|> return (ty.arbitrary_int)),
  ReadWhitespaces,
  cond ← ReadVal,
  ReadWhitespaces,
  ch ',',
  ReadWhitespaces,
  valty ← (ReadType <|> return (ty.arbitrary_int)),
  ReadWhitespaces,
  v1 ← ReadVal,
  ReadWhitespaces,
  ch ',',
  ReadWhitespaces,
  valty ← (ReadType <|> return (ty.arbitrary_int)),
  ReadWhitespaces,
  v2 ← ReadVal,
  ReadWhitespaces,
  ReadLinebreaks,
  return (instruction.selectop lhs condty cond valty v1 v2)

-- Reads "icmp" instruction.
def ReadICmpInst (lhs:reg): parser instruction :=
  do
  str "icmp",
  ReadWhitespaces,
  cond ← ReadICmpCond,
  ReadWhitespaces,
  thety ← (ReadType <|> return (ty.arbitrary_int)),
  ReadWhitespaces,
  v1 ← ReadVal,
  ReadWhitespaces,
  ch ',',
  ReadWhitespaces,
  v2 ← ReadVal,
  ReadWhitespaces,
  ReadLinebreaks,
  return (instruction.icmpop thety lhs cond v1 v2)

-- Reads "freeze" instruction.
def ReadFreezeInst (lhs:reg): parser instruction :=
  do
  str "freeze",
  ReadWhitespaces,
  v ← ReadVal,
  ReadWhitespaces,
  ReadLinebreaks,
  return (instruction.unaryop lhs uopcode.freeze (ty.arbitrary_int) v (ty.arbitrary_int))

-- Reads an instruction.
def ReadInstruction: parser instruction :=
  do
  ReadWhitespaces,
  lhs ← ReadReg,
  ReadWhitespaces,
  str "=",
  ReadWhitespaces,
  (ReadBinaryInst lhs "add" bopcode.add) <|>
  (ReadBinaryInst lhs "sub" bopcode.sub) <|>
  (ReadBinaryInst lhs "mul" bopcode.mul) <|>
  (ReadBinaryInst lhs "udiv" bopcode.udiv) <|>
  (ReadBinaryInst lhs "urem" bopcode.urem) <|>
  (ReadBinaryInst lhs "sdiv" bopcode.sdiv) <|>
  (ReadBinaryInst lhs "srem" bopcode.srem) <|>
  (ReadBinaryInst lhs "shl" bopcode.shl) <|>
  (ReadBinaryInst lhs "ashr" bopcode.ashr) <|>
  (ReadBinaryInst lhs "lshr" bopcode.lshr) <|>
  (ReadBinaryInst lhs "and" bopcode.and) <|>
  (ReadBinaryInst lhs "or" bopcode.or) <|>
  (ReadBinaryInst lhs "xor" bopcode.xor) <|>
  (ReadCastInst lhs "zext" uopcode.zext) <|>
  (ReadCastInst lhs "sext" uopcode.sext) <|>
  (ReadCastInst lhs "trunc" uopcode.trunc) <|>
  (ReadSelectInst lhs) <|>
  (ReadICmpInst lhs) <|>
  (ReadFreezeInst lhs) <|>
  failure

-- Reads a program.
def ReadProgram: parser program :=
  do
  ReadWhitespaces,
  insts ← many ReadInstruction,
  return (program.mk insts)

def ReadTransformation: parser transformation :=
  do
  ReadWhitespaces, str "Name:",
  name ← ReadLine,
  p1 ← ReadProgram,
  str "=>",
  p2 ← ReadProgram,
  return (transformation.mk name p1 p2)

def ReadTransformations: parser (list transformation) :=
  do
  tfs ← many ReadTransformation,
  return tfs
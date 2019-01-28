-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

/-
Semantics of LLVM IR
-/
import .lang
import .common
import .ops
import system.io

structure irsem :=
(intty:size → Type)
(poisonty:Type)
-- This is for UB as well
(boolty:Type)

namespace irsem
section

open io


parameter (sem : irsem)

-- uint_like types
variable [ihc:has_comp sem.intty sem.boolty]
variable [ioc:has_overflow_check sem.intty sem.boolty]
variable [iul:uint_like sem.intty]
-- poison types
variable [pbl:bool_like sem.poisonty]
variable [p2b:has_coe sem.poisonty sem.boolty]
-- bool types
variable [bbl:bool_like sem.boolty]
variable [b2i:has_coe sem.boolty (sem.intty size.one)]
variable [bhi:Π (sz:size), has_ite sem.boolty (sem.intty sz)]
variable [bhi2:has_ite sem.boolty sem.poisonty]


inductive valty
| ival: Π (sz:size), sem.intty sz → sem.poisonty → valty

-- A register file.
def regfile := list (string × valty)
def regfile.get (r:regfile) (s:string) : option valty :=
  match (list.filter (λ (itm:string × valty), s = itm.fst) r) with
  | (name,val)::_ := some val
  | nil := none
  end

def regfile.update (r:regfile) (s:string) (v:valty) :=
  (s,v)::r

def regfile.empty : regfile :=
  []

def regfile.apply_to_values (r:regfile) (f:valty → valty): regfile :=
  list.map (λ x:(string × valty), (x.1, f x.2)) r
 
def regfile.regnames (r:regfile) : list string :=
  list.map (λ x:(string × valty), x.1) r

def regfile.to_string' [has_to_string valty] (rs:regfile) : string :=
  list.foldr
      (λ (itm:string × valty) (befst:string),
          befst ++ (itm.1) ++ ":" ++ (to_string itm.2) ++ ",\n")
      "" rs

include ihc
include ioc
include iul
include bbl
include pbl
include p2b
include b2i
include bhi
include bhi2

-- Current state of execution.
-- 'state' is already defined, Lean says.
def irstate := sem.boolty × regfile

def irstate.empty : irstate :=
  (bbl.tt, regfile.empty)

section
variable (s:irstate)
def irstate.getreg (name:string) : option valty :=
  regfile.get s.2 name

def irstate.regnames : list string :=
  regfile.regnames s.2

def irstate.updatereg (name:string) (v:valty)
  : irstate :=
  (s.1, regfile.update s.2 name v)

def irstate.updateub (u:sem.boolty) : irstate :=
  (s.1 & u, s.2)

def irstate.setub (u:sem.boolty) : irstate :=
  (u, s.2)

def irstate.getub : sem.boolty :=
  s.1

def irstate.apply_to_values (f:valty → valty): irstate :=
  (s.1, regfile.apply_to_values s.2 f)

def irstate.to_string' [has_to_string valty] [has_to_string sem.poisonty] [has_to_string sem.boolty]
    : string :=
    "(Is not UB?: " ++ to_string(s.1) ++ ",\n" ++ regfile.to_string' s.2 ++ ")"
end

-- Get current value from syntactic val (either register or constant).
-- For example, if val is a register "x", get_value loads "x" and returns
-- the value.
def get_value (s:irstate) (v:operand) (t:ty): option valty :=
  match v with
  | operand.reg (reg.r name) := (irstate.getreg s name)
  | operand.const (const.int z) :=
    match t with
    | ty.int bitsz :=
      if h:(0 < bitsz) then
        let sz := (⟨bitsz, h⟩:size),
            intgen := @uint_like.from_z sem.intty iul sz,
            nopoison := pbl.tt in
        if h0:(within_signed_range sz z) then
          -- e.g. -128 ≤ z ≤ 127 (if bitsz is 8)
          some (valty.ival sz (intgen z) nopoison)
        else if h1:(↑(int_min_nat sz) ≤ z ∧ z ≤ (all_one_nat sz)) then
          -- e.g. 128 ≤ z ≤ 255 (if bitsz is 8)
          -- Convert into the corresponding negative number.
          some (valty.ival sz (intgen (z - int.of_nat (2 ^ bitsz))) nopoison)
        else
          none -- the constant does not fit in bitsize!
      else
          none -- bitsize should be always larger than 0!
    | ty.arbitrary_int := none -- arbitrary_int should not appear at execution time.
    end
  end

-- Cast bool to poison
@[reducible]
def b2p (b:sem.boolty) : sem.poisonty :=
    has_ite.ite b (pbl.tt) (pbl.ff)

-- If v1 ≠ v2, yields poison
@[reducible]
def neq2p {sz:size} (v1 v2:sem.intty sz) : sem.poisonty :=
    b2p (v1 =_{sem.boolty} v2)

-- If v1 = v2, yields poison
@[reducible]
def eq2p {sz:size} (v1 v2:sem.intty sz) : sem.poisonty :=
    b2p (v1 ≠_{sem.boolty} v2)

-- Performs given binary operation.
def bop_val (sz:size) : bopcode → sem.intty sz → sem.intty sz → sem.intty sz
| bopcode.add n1 n2 := n1 + n2
| bopcode.sub n1 n2 := n1 - n2
| bopcode.mul n1 n2 := n1 * n2
| bopcode.udiv n1 n2 := n1 /u n2
| bopcode.urem n1 n2 := n1 %u n2
| bopcode.sdiv n1 n2 := n1 / n2
| bopcode.srem n1 n2 := n1 % n2
| bopcode.and n1 n2 := n1 & n2
| bopcode.or n1 n2 := n1 |b n2
| bopcode.xor n1 n2 := n1 ^b n2
| bopcode.shl n1 n2 := n1 << n2
| bopcode.lshr n1 n2 := n1 >>l n2
| bopcode.ashr n1 n2 := n1 >>a n2

-- Returns true if it fits into the range of signed/unsigned integer
def bop_overflow_check (nsw:bool) (sz:size)
  (bc:bopcode) (op1:sem.intty sz) (op2:sem.intty sz)
  : sem.poisonty :=
  b2p (match bc with
    | bopcode.add := has_overflow_check.add_chk sem.boolty nsw op1 op2
    | bopcode.sub := has_overflow_check.sub_chk sem.boolty nsw op1 op2
    | bopcode.mul := has_overflow_check.mul_chk sem.boolty nsw op1 op2
    | bopcode.shl := has_overflow_check.shl_chk sem.boolty nsw op1 op2
    -- If the instruction is well-typed, it is unreachable here.
    | _ := has_overflow_check.mul_chk sem.boolty nsw op1 op2
  end)

-- Returns true if it fits into the range of signed/unsigned integer
def bop_exact_check (sz:size) (bc:bopcode) (op1:sem.intty sz) (op2:sem.intty sz)
  : sem.poisonty :=
  let zero:sem.intty sz := uint_like.zero sz,
      sz':sem.intty sz  := uint_like.from_z sz sz,
      op2' := op2 %u sz' in
  match bc with
  | bopcode.sdiv := eq2p (op1 % op2) zero
  | bopcode.srem := eq2p (op1 % op2) zero
  | bopcode.udiv := eq2p (op1 %u op2) zero
  | bopcode.urem := eq2p (op1 %u op2) zero
  | bopcode.ashr := eq2p ((op1 >>a op2') << op2') op1
  | bopcode.lshr := eq2p ((op1 >>l op2') << op2') op1
  | _ := eq2p op1 op2 -- Unreachable
  end

-- Checks whether the binary operation returns poison.
def bop_poison_flag (sz:size) (code:bopcode) (flag:bopflag) (v1:sem.intty sz) (v2:sem.intty sz)
  : sem.poisonty :=
  ~ (match flag with
  | bopflag.nsw := bop_overflow_check tt sz code v1 v2
  | bopflag.nuw := bop_overflow_check ff sz code v1 v2
  | bopflag.exact := bop_exact_check sz code v1 v2
  end)

def bop_poison (sz:size) (code:bopcode) (v1:sem.intty sz) (v2:sem.intty sz)
  : sem.poisonty :=
  let sz':sem.intty sz := uint_like.from_z sz sz,
      res := match code with
    | bopcode.shl := v2 <u_{sem.boolty} sz'
    | bopcode.ashr := v2 <u_{sem.boolty} sz'
    | bopcode.lshr := v2 <u_{sem.boolty} sz'
    | _ := bbl.tt
    end in
  b2p res

-- Checks whether the binary operation yields UB.
def bop_ub (sz:size) (code:bopcode)
  (op1:sem.intty sz) (op1p:sem.poisonty) (op2:sem.intty sz) (op2p:sem.poisonty)
  : sem.boolty :=
  if bop_isdiv code = tt then
    let zero:sem.intty sz :=   uint_like.zero sz,
        allone:sem.intty sz := uint_like.allone sz,
        intmin:sem.intty sz := uint_like.signonly sz in
    let cmp := (eq2p op2 zero) in
    let signeddiv := 
      if code = bopcode.sdiv ∨ code = bopcode.srem then
        (op1p & (eq2p op1 intmin)) |b (eq2p op2 allone)
      else pbl.tt in
    op2p & cmp & signeddiv
  else bbl.tt

def bop_poison_all (sz:size) (code:bopcode) (flags:list bopflag)
  (op1:sem.intty sz) (op2:sem.intty sz) : sem.poisonty :=
  list.foldr (λ flag p1, p1 & (bop_poison_flag sz code flag op1 op2))
      (bop_poison sz code op1 op2) flags

-- Semantics of binary operator instruction.
def bop (sz:size) (code:bopcode) (flags:list bopflag)
  (op1:sem.intty sz) (op1p:sem.poisonty)
  (op2:sem.intty sz) (op2p:sem.poisonty)
  : (sem.boolty × (sem.intty sz × sem.poisonty)) :=
  -- 'cast' is needed to cast 'vector sz2' type into 'vector sz1'. 
  let res := bop_val sz code op1 op2,
    op_poison := op1p & op2p,
    poison := (bop_poison_all sz code flags op1 op2) & op_poison,
    ub := bop_ub sz code op1 op1p op2 op2p in
  (ub, (res, poison))

-- Semantics of cast instruction.
def castop (fromsz:size) (code:uopcode)
  (op1:sem.intty fromsz) (op1p:sem.poisonty) (tosz:size)
  : (sem.intty tosz × sem.poisonty) :=
  if fromsz.val < tosz.val then
    (match code with
    | uopcode.zext := uint_like.zext fromsz tosz op1
    | uopcode.sext := uint_like.sext fromsz tosz op1
    | _ := uint_like.sext fromsz tosz op1 -- Unreachable
    end, op1p)
  else if fromsz.val = tosz.val then
    (uint_like.zero tosz, op1p) -- unreacahble
  else
    (uint_like.trunc fromsz tosz op1, op1p)

-- Semantics of icmp instruction.
def icmpop (sz:size) (cond:icmpcond) (a:sem.intty sz) (ap:sem.poisonty)
  (b:sem.intty sz) (bp:sem.poisonty)
  : (sem.intty (size.one) × sem.poisonty) :=
  let res := match cond with
  | icmpcond.eq := a =_{sem.boolty} b
  | icmpcond.ne := a ≠_{sem.boolty} b
  | icmpcond.ugt := a >u_{sem.boolty} b
  | icmpcond.uge := a ≥u_{sem.boolty} b
  | icmpcond.ult := a <u_{sem.boolty} b
  | icmpcond.ule := a ≤u_{sem.boolty} b
  | icmpcond.sgt := a >_{sem.boolty} b
  | icmpcond.sge := a ≥_{sem.boolty} b
  | icmpcond.slt := a <_{sem.boolty} b
  | icmpcond.sle := a ≤_{sem.boolty} b
  end in
  (res, ap & bp)

-- Semantics of select instruction.
def selectop (cond:sem.intty size.one) (pcond:sem.poisonty) (sz:size)
  (a:sem.intty sz) (ap:sem.poisonty) (b:sem.intty sz) (bp:sem.poisonty)
  : (sem.intty sz × sem.poisonty) :=
  let one:sem.intty _ := uint_like.from_z size.one 1,
      eqtest := cond =_{sem.boolty} one in
  let c  := @has_ite.ite sem.boolty (sem.intty sz) (bhi sz) eqtest a b in
  let cp := has_ite.ite eqtest ap bp in
  (c, pcond & cp)


/-
 - Execution of a single instruction
 -/
def to_ival {sz:size} (xp:sem.intty sz × sem.poisonty ) :=
  valty.ival sz xp.1 xp.2

-- Execution of bop, but it fails if type check fails
def step_bop (v1 v2:valty) (code:bopcode)
  (bflags:list bopflag) (s1:irstate) (lhsn:string) : option irstate :=
  match v1,v2 with
  | (valty.ival sz1 n1 p1), (valty.ival sz2 n2 p2) :=
    if H:sz1 = sz2 then do
      let (u3, x) := (bop sz1 code bflags n1 p1 (cast (by rw H) n2) p2) in
      some (irstate.updatereg (irstate.updateub s1 u3)
              lhsn (to_ival x))
    else none
  end

-- Execution of unaryop, but it fails if type check fails
def step_unaryop (v1:valty) (code:uopcode)
  (toisz:nat) (s1:irstate) (lhsn:string) : option irstate :=
  match v1, code with
  | _, uopcode.freeze := none -- Not implemented yet
  | (valty.ival sz1 n1 p1), _ :=
    if H:toisz > 0 then
      let tosz := subtype.mk toisz H in
      some (irstate.updatereg s1 lhsn (to_ival (castop sz1 code n1 p1 tosz)))
    else -- isz cannot be 0 size!
      none
  end

-- Execution of bop, but it fails if type check fails
def step_icmpop (v1 v2:valty) (cond:icmpcond)
  (s1:irstate) (lhsn:string) : option irstate :=
  match v1,v2 with
  | (valty.ival sz1 n1 p1), (valty.ival sz2 n2 p2) :=
    if H:sz1 = sz2 then
      some (irstate.updatereg s1 lhsn
              (to_ival (icmpop sz1 cond n1 p1 (cast (by rw H) n2) p2)))
    else
      none
  end

-- Execution of bop, but it fails if type check fails
def step_selectop (vcond v1 v2:valty)
  (s1:irstate) (lhsn:string) : option irstate :=
  match vcond,v1,v2 with
  | (valty.ival szcond ncond pcond),
    (valty.ival sz1 n1 p1), (valty.ival sz2 n2 p2) :=
    if Hc:szcond = size.one then
      if H:sz1 = sz2 then
        some (irstate.updatereg s1 lhsn (to_ival
            (selectop (cast (by rw Hc) ncond) pcond
            sz1 n1 p1 (cast (by rw H) n2) p2 )))
      else none
    else none
  end

def step_exe (s1:irstate) (i:instruction) : option irstate :=
  match i with
  | instruction.binop retty (reg.r lhsn) code bflags op1 op2 :=
    do
    v1 ← get_value s1 op1 retty,
    v2 ← get_value s1 op2 retty,
    step_bop v1 v2 code bflags s1 lhsn
  | instruction.unaryop (reg.r lhsn) code fromty op1 toty@(ty.int toisz):=
    do
    v1 ← get_value s1 op1 fromty,
    step_unaryop v1 code toisz s1 lhsn
  | instruction.icmpop opty (reg.r lhsn) cond op1 op2 :=
    do
    v1 ← get_value s1 op1 opty,
    v2 ← get_value s1 op2 opty,
    step_icmpop v1 v2 cond s1 lhsn
  | instruction.selectop (reg.r lhsn) condty cond vty op1 op2 :=
    do
    vcond ← get_value s1 cond condty,
    v1 ← get_value s1 op1 vty,
    v2 ← get_value s1 op2 vty,
    step_selectop vcond v1 v2 s1 lhsn
  | _ := none -- Stuck!
  end

-- Execution of a program
def bigstep_exe (inits:irstate) (p:program): option irstate :=
  list.foldl (λ befst inst,
      match befst with
      | none := none -- Stuck!
      | some st := step_exe st inst
      end) (some inits) (p.insts)

end
end irsem

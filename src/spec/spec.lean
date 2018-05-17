-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import ..smtexpr
import ..bitvector
import ..irsem
import ..irsem_exec
import ..irsem_smt
import ..freevar
import ..verifyopt
import .lemmas_basic
import smt2.syntax
import smt2.solvers.z3
import system.io


namespace spec

-- This inductive predicate is needed to formally define
-- the relation between sbitvec ops and bitvector ops.
-- This can be used to prove ex. ∀ s b, equiv s b → equiv (optimize s) b

mutual inductive b_equiv, bv_equiv
with b_equiv : sbool → bool → Prop
| tt: b_equiv sbool.tt bool.tt

| ff: b_equiv sbool.ff bool.ff

| and1: ∀ (s1 s2:sbool) (b1 b2:bool),
    b_equiv s1 b1 → (b1 = tt → b_equiv s2 b2) → b_equiv (s1.and s2) (band b1 b2)

| and2: ∀ (s1 s2:sbool) (b1 b2:bool),
    b_equiv s2 b2 → (b2 = tt → b_equiv s1 b1) → b_equiv (s1.and s2) (band b1 b2)

| or1: ∀ (s1 s2:sbool) (b1 b2:bool),
    b_equiv s1 b1 → (b1 = ff → b_equiv s2 b2) → b_equiv (s1.or s2) (bor b1 b2)

| or2: ∀ (s1 s2:sbool) (b1 b2:bool),
    b_equiv s2 b2 → (b2 = ff → b_equiv s1 b1) → b_equiv (s1.or s2) (bor b1 b2)

| xor: ∀ (s1 s2:sbool) (b1 b2:bool),
    b_equiv s1 b1 → b_equiv s2 b2 → b_equiv (s1.xor s2) (bxor b1 b2)

| not: ∀ (s:sbool) (b:bool),
    b_equiv s b → b_equiv (s.not) (bnot b)

| ite: ∀ (sc s1 s2: sbool) (bc b1 b2:bool),
    b_equiv sc bc → b_equiv s1 b1 → b_equiv s2 b2 →
    b_equiv (sbool.ite sc s1 s2) (cond bc b1 b2)

| eq: ∀ (sz:size) (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → b_equiv (sbool.eqbv s1 s2) (bitvector.eq b1 b2)

| ne: ∀ (sz:size) (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → b_equiv (sbool.nebv s1 s2) (bitvector.ne b1 b2)

| ult: ∀ (sz:size) (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → b_equiv (sbool.ult s1 s2) (bitvector.ult b1 b2)

| ule: ∀ (sz:size) (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → b_equiv (sbool.ule s1 s2) (bitvector.ule b1 b2)

| slt: ∀ (sz:size) (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → b_equiv (sbool.slt s1 s2) (bitvector.slt b1 b2)

| sle: ∀ (sz:size) (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → b_equiv (sbool.sle s1 s2) (bitvector.sle b1 b2)


with bv_equiv : Π {sz:size}, sbitvec sz → bitvector sz → Prop
| const: ∀ {sz:size} (n:nat) (H:n < 2^sz.val), bv_equiv
        (sbitvec.const sz n) ⟨n, H⟩

| add: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → bv_equiv (s1.add s2) (b1.add b2)

| sub: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → bv_equiv (s1.sub s2) (b1.sub b2)

| mul: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → bv_equiv (s1.mul s2) (b1.mul b2)

| and: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → bv_equiv (s1.and s2) (b1.bitwise_and b2)

| or: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → bv_equiv (s1.or s2) (b1.bitwise_or b2)

| xor: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → bv_equiv (s1.xor s2) (b1.bitwise_xor b2)

| shl: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 →
    (bitvector.ult b2 (bitvector.of_int sz (int.of_nat sz.val)) = tt) →
    bv_equiv (s1.shl s2) (b1.shl b2)

| lshr: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → 
    (bitvector.ult b2 (bitvector.of_int sz (int.of_nat sz.val)) = tt) →
    bv_equiv (s1.lshr s2) (b1.lshr b2)

| ashr: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 → 
    (bitvector.ult b2 (bitvector.of_int sz (int.of_nat sz.val)) = tt) →
    bv_equiv (s1.ashr s2) (b1.ashr b2)

| udiv: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 →
    (bitvector.ne b2 (bitvector.zero sz) = tt) → -- Div by 0 is UB
    bv_equiv (s1.udiv s2) (b1.udiv b2)

| urem: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 →
    (bitvector.ne b2 (bitvector.zero sz) = tt) → -- Div by 0 is UB
    bv_equiv (s1.urem s2) (b1.urem b2)

| sdiv: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 →
    (bitvector.ne b2 (bitvector.zero sz) = tt) → -- Div by 0 is UB
    (bitvector.ne b1 (bitvector.int_min sz) = tt)
    ∨ (bitvector.ne b2 (bitvector.all_one sz) = tt) → -- (INT_MIN / -1 is UB)
    bv_equiv (s1.sdiv s2) (b1.sdiv b2)

| srem: ∀ {sz:size} (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    bv_equiv s1 b1 → bv_equiv s2 b2 →
    (bitvector.ne b2 (bitvector.zero sz) = tt) → -- Div by 0 is UB
    (bitvector.ne b1 (bitvector.int_min sz) = tt)
    ∨ (bitvector.ne b2 (bitvector.all_one sz) = tt) → -- (INT_MIN / -1 is UB)
    bv_equiv (s1.srem s2) (b1.srem b2)

| ite: ∀ {sz:size} (sc: sbool) (bc:bool) (s1 s2:sbitvec sz) (b1 b2:bitvector sz),
    b_equiv sc bc → (bc = tt → bv_equiv s1 b1) → (bc = ff → bv_equiv s2 b2) →
    bv_equiv (sbitvec.ite sc s1 s2) (cond bc b1 b2)

| of_bool: ∀ (s:sbool) (b:bool),
    b_equiv s b → bv_equiv (sbitvec.of_bool s) (bitvector.of_bool b)

| trunc: ∀ (fromsz tosz:size) (H:tosz.val < fromsz.val) (s:sbitvec fromsz) (b:bitvector fromsz),
    bv_equiv s b → bv_equiv (sbitvec.trunc tosz s) (bitvector.trunc tosz b)

| zext: ∀ (fromsz tosz:size) (H:tosz.val > fromsz.val)
            (s:sbitvec fromsz) (b:bitvector fromsz),
    bv_equiv s b → bv_equiv (sbitvec.zext tosz s) (bitvector.zext tosz b)

| sext: ∀ (fromsz tosz:size) (H:tosz.val > fromsz.val)
            (s:sbitvec fromsz) (b:bitvector fromsz),
    bv_equiv s b → bv_equiv (sbitvec.sext tosz s) (bitvector.sext tosz b)


open irsem
open freevar
open opt

@[reducible]
def intty_smt := irsem_smt.intty
@[reducible]
def intty_exec := irsem_exec.intty

@[reducible]
def valty_smt := irsem_smt.valty
@[reducible]
def valty_exec := irsem_exec.valty

@[reducible]
def equals_size : valty_smt → valty_exec → bool
| (irsem.valty.ival sz1 v1 p1) (irsem.valty.ival sz2 v2 p2) := sz1 = sz2

@[reducible]
def poisonty_smt := irsem_smt.poisonty
@[reducible]
def poisonty_exec := irsem_exec.poisonty

-- Equivalence of two poison values.
inductive poison_equiv:
  irsem_smt.poisonty → irsem_exec.poisonty → Prop
| intro: Π (ps:poisonty_smt) (pe:poisonty_exec),
  b_equiv ps pe → poison_equiv ps pe

-- Equivalence of (concrete-value, poison)
inductive val_equiv: valty_smt → valty_exec → Prop
| poison_intty: Π (szs:size) (vs:intty_smt szs) (ps:poisonty_smt)
    (sze:size) (ve:intty_exec sze) (pe:poisonty_exec),
  poison_equiv ps pe →
  szs = sze →
  pe = irsem_exec.pbl.ff →
  val_equiv (irsem.valty.ival szs vs ps) (irsem.valty.ival sze ve pe)
| concrete_intty: Π (sz:size) (vs:intty_smt sz) (ps:poisonty_smt)
                    (ve:intty_exec sz) (pe:poisonty_exec),
  poison_equiv ps pe →
  bv_equiv vs ve →
  pe = irsem_exec.pbl.tt →
  val_equiv (irsem.valty.ival sz vs ps) (irsem.valty.ival sz ve pe)

@[reducible]
def regfile_smt := irsem_smt.regfile
@[reducible]
def regfile_exec := irsem_exec.regfile

-- Equivalence of two Register files.
inductive regfile_equiv: regfile_smt → regfile_exec → Prop
| empty: ∀ rs re,
  rs = regfile.empty irsem_smt →
  re = regfile.empty irsem_exec →
  regfile_equiv rs re
| update: ∀ rs re vs ve rname rs' re',
  regfile_equiv rs re →
  val_equiv vs ve →
  rs' = regfile.update irsem_smt rs rname vs →
  re' = regfile.update irsem_exec re rname ve →
  regfile_equiv rs' re'

@[reducible]
def none_or_some {α β:Type} (os: option α) (oe:option β) (P:α → β → Prop) :=
  (os = none ∧ oe = none) ∨
  (∃ s e, os = some s ∧ oe = some e ∧ (P s e))

def regfile_sametypes (rs:regfile_smt) (re:regfile_exec) :=
  ∀ (rname:string) os oe,
      os = regfile.get irsem_smt rs rname ∧
      oe = regfile.get irsem_exec re rname →
    none_or_some os oe (λ vs ve, equals_size vs ve = tt)

def irstate_smt := irsem_smt.irstate
def irstate_exec := irsem_exec.irstate

@[reducible]
def has_no_ub: irstate_exec → bool
| (ubs, rs) := ubs

-- Equivalence of two IR states.
inductive irstate_equiv: irstate_smt → irstate_exec → Prop
| noub: ∀ ubs ube rs re,
  regfile_equiv rs re →
  b_equiv ubs ube →
  ube = irsem_exec.bbl.tt →
  irstate_equiv (ubs, rs) (ube, re)
| ub: ∀ ubs ube rs re, -- if UB, register files may differ.
  b_equiv ubs ube →
  ube = irsem_exec.bbl.ff →
  regfile_sametypes rs re → -- but they should have same type!
  irstate_equiv (ubs, rs) (ube, re)


-- Smallstep preserves equivalence between two states.
def step_both := ∀ {ss:irstate_smt} {se:irstate_exec} {i:instruction}
    {oss':option irstate_smt} {ose':option irstate_exec}
    (HSTEQ: irstate_equiv ss se)
    (HOSS': oss' = step_exe irsem_smt ss i)
    (HOSE': ose' = step_exe irsem_exec se i),
  none_or_some oss' ose' (λ ss' se', irstate_equiv ss' se')


-- Bigstep on an open program
def encode (ss:irstate_smt) (se:irstate_exec) (η:freevar.env) :=
    irstate_equiv (η⟦ss⟧) se

def bigstep_both:= ∀ ss se p oss' ose' η
    (HENC:encode ss se η)
    (HOSS': oss' = bigstep_exe irsem_smt ss p)
    (HOSE': ose' = bigstep_exe irsem_exec se p),
  none_or_some oss' ose' (λ ss' se', encode ss' se' η)

def init_state_encode:= ∀ (freevars:list (string × ty)) (sg sg':std_gen) ise iss
    (HUNQ: list.unique $ freevars.map prod.fst)
    (HIE:(ise, sg') = create_init_state_exec freevars sg)
    (HIS:iss = create_init_state_smt freevars),
  ∃ η, encode iss ise η

-- Refinement
inductive val_refines : valty_exec → valty_exec → Prop
| poison_intty: ∀ sz (isrc:intty_exec sz) psrc (itgt:intty_exec sz) ptgt,
    psrc = irsem_exec.pbl.ff →
    val_refines (valty.ival sz isrc psrc) (valty.ival sz itgt ptgt)
| concrete_intty: ∀ sz (isrc:intty_exec sz) psrc (itgt:intty_exec sz) ptgt,
    psrc = irsem_exec.pbl.tt →
    ptgt = irsem_exec.pbl.tt →
    isrc = itgt →
    val_refines (valty.ival sz isrc psrc) (valty.ival sz itgt ptgt)

def check_val_exec_spec:=
  ∀ vsrc vtgt (H:opt.check_val irsem_exec vsrc vtgt = some tt),
    val_refines vsrc vtgt


inductive ub_refines: irstate_exec → irstate_exec → Prop
| noub: ∀ src tgt,
  irstate.getub irsem_exec src = irsem_exec.bbl.tt →
  irstate.getub irsem_exec tgt = irsem_exec.bbl.tt →
  ub_refines src tgt
| ub: ∀ src tgt,
  irstate.getub irsem_exec src = irsem_exec.bbl.ff →
  ub_refines src tgt

def irstate_refines (se:irstate_exec) (se':irstate_exec): Prop :=
  ub_refines se se' ∧
  ∀ r, none_or_some (irstate.getreg irsem_exec se r)
                    (irstate.getreg irsem_exec se' r)
                    (λ v1 v2, val_refines v1 v2)

def root_refines (ssrc:irstate_exec) (stgt:irstate_exec) (root:string): Prop :=
  ub_refines ssrc stgt ∧
  (irstate.getub irsem_exec ssrc = irsem_exec.bbl.tt →
    ∃ v1 v2, some v1 = irstate.getreg irsem_exec ssrc root ∧
             some v2 = irstate.getreg irsem_exec stgt root ∧
             val_refines v1 v2)

def refines_finalstate (psrc ptgt:program) (se0:irstate_exec) :=
  ∀ se se',
    some se  = bigstep_exe irsem_exec se0 psrc →
    some se' = bigstep_exe irsem_exec se0 ptgt →
    irstate_refines se se'

def root_refines_finalstate (psrc ptgt:program) (se0:irstate_exec) (root:string):=
  ∀ se se',
    some se  = bigstep_exe irsem_exec se0 psrc →
    some se' = bigstep_exe irsem_exec se0 ptgt →
    root_refines se se' root

def refines_smt (psrc ptgt:program) := ∀ (η:freevar.env) ss0 se0,
    encode ss0 se0 η → refines_finalstate psrc ptgt se0

def root_refines_smt (psrc ptgt:program) (ss0:irstate_smt) (root:string) :=
  ∀ (η:freevar.env) se0,
    encode ss0 se0 η → root_refines_finalstate psrc ptgt se0 root

def refines_single_reg_correct := ∀ (psrc ptgt:program)
    (root:string) (ss0:irstate_smt) sb
    (HSREF:some sb = check_single_reg0 irsem_smt psrc ptgt root ss0)
    (HEQ:∀ (η0:freevar.env) e, b_equiv (η0⟦sb⟧) e → e = tt),
  root_refines_smt psrc ptgt ss0 root

end spec

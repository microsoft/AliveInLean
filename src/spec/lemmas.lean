-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import ..smtexpr
import ..smtcompile
import ..bitvector
import .spec
import .lemmas_basic
import tactic.interactive


namespace spec

open smt
open irsem
open spec

-- unfold
meta def unfold_ops: tactic unit :=
  `[ try { unfold has_eq.eq },
     try { unfold has_comp.eq },
     try { unfold has_ne.ne },
     try { unfold has_comp.ne },
     try { unfold has_and.and },
     try { unfold has_ult.ult },
     try { unfold has_comp.ult },
     try { unfold has_ule.ule },
     try { unfold has_comp.ule },
     try { unfold has_ugt.ugt },
     try { unfold has_comp.ult },
     try { unfold has_uge.uge },
     try { unfold has_comp.ule },
     try { unfold has_slt.slt },
     try { unfold has_comp.slt },
     try { unfold has_sle.sle },
     try { unfold has_comp.sle },
     try { unfold has_sgt.sgt },
     try { unfold has_comp.slt },
     try { unfold has_sge.sge },
     try { unfold has_comp.sle } ]

meta def unfold_lops_at_all: tactic unit :=
  `[ try { unfold has_eq.eq at * },
     try { unfold has_comp.eq at * },
     try { unfold has_ne.ne at * },
     try { unfold has_comp.ne at * },
     try { unfold has_and.and at * },
     try { unfold has_or.or at * } ]

-- Constant sbitvec is never optimized.
lemma sbitvec_cons_notoptimized: ∀ sz z,
optimize_add_zero (sbitvec.const sz z) = (sbitvec.const sz z) :=
begin
  intros sz z,
  unfold optimize_add_zero
end

-- bitvector eq

lemma bveq: ∀ {sz:size} {b1 b2:bitvector sz},
  bitvector.eq b1 b2 = tt ↔ b1 = b2
:= begin
  intros,
  split,
  {
    intros H,
    cases b1, cases b2,
    unfold bitvector.eq at H,
    simp at H,
    assumption
  },{
    intros H,
    rw H, unfold bitvector.eq, simp
  }
end

lemma bvneq: ∀ (sz:size) (b1 b2:bitvector sz),
  bitvector.eq b1 b2 = ff ↔ b1 ≠ b2
:= begin
  intros sz b1 b2,
  split,
  { -- →
    intros H,
    cases b1,
    cases b2,
    unfold bitvector.eq at H,
    simp at H,
    apply H
  }, { -- ←
    intros H,
    cases b1,
    cases b2,
    unfold bitvector.eq,
    simp,
    apply H
  }
end

lemma bvneq_l : ∀ {sz:size} {b1 b2:bitvector sz},
  bitvector.eq b1 b2 = ff → b1 ≠ b2
:= begin intros, rw ← bvneq, assumption end

lemma bvneq_r : ∀ {sz:size} {b1 b2:bitvector sz},
  b1 ≠ b2 → bitvector.eq b1 b2 = ff
:= begin intros, rw bvneq, assumption end

lemma bvneq_from_z: ∀ (sz:size) (n m:int),
  n ≠ m → 0 ≤ n ∧ n < int.of_nat (2^sz.val)
        ∧ 0 ≤ m ∧ m < int.of_nat (2^sz.val) →
  bitvector.eq (uint_like.from_z sz n)
               (uint_like.from_z sz m) = ff
:= begin
  intros sz n m H H1,
  cases H1 with H1 H2,
  cases H2 with H2 H3,
  cases H3 with H3 H4,
  unfold uint_like.from_z,
  cases n; cases m,
  {
    unfold bitvector.of_int,
    unfold bitvector.eq,
    simp,
    intros H0,
    injection H0,
    have Hz := int.coe_nat_lt_coe_nat_iff,
    unfold_coes at Hz,
    rw Hz at H2,
    rw Hz at H4,
    rw nat.mod_eq_of_lt at h_1; try { assumption },
    rw nat.mod_eq_of_lt at h_1; try { assumption },
    apply H, congr, assumption,
  },
  { cases H3 },
  { cases H1 },
  { cases H3 }
end

lemma bvult_mod_sz: ∀ (sz:size) (eb:bitvector sz),
  bitvector.ult (eb%u uint_like.from_z sz ↑sz)
                (bitvector.of_int sz (int.of_nat (sz.val))) = tt
:= begin
  intros,
  cases sz, unfold_coes, unfold uint_like.from_z, unfold bitvector.ult,
  unfold bitvector.of_int, cases eb, simp, unfold has_umod.umod,
  unfold uint_like.urem, unfold bitvector.urem, unfold_coes, simp,
  rw nat.mod_pow2, rw nat.mod_eq_of_lt,
  {
    apply nat.mod_lt, assumption,
  },
  {
    apply lt_trans,
    { apply nat.mod_lt, assumption },
    apply nat.lt_pow2
  }
end

-- Lemmas regarding bvequiv

lemma bvequiv_of_int: ∀ sz x,
  bv_equiv (sbitvec.of_int sz x) (bitvector.of_int sz x)
:= begin
  intros,
  cases x; unfold sbitvec.of_int,
  { unfold bitvector.of_int,
    apply bv_equiv.const },
  {
    unfold bitvector.of_int,
    apply bv_equiv.const
  }
end

lemma bvequiv_from_z: ∀ (sz:size) n,
  bv_equiv (uint_like.from_z sz n)
           (uint_like.from_z sz n)
:= begin
  intros,
  unfold uint_like.from_z, apply bvequiv_of_int
end

lemma bvequiv_urem: ∀ (sz:size) (sb:sbitvec sz) eb
    (HA:bv_equiv sb eb),
  bv_equiv (sb%u uint_like.from_z sz sz.val)
           (eb%u uint_like.from_z sz sz.val)
:= begin
  intros,
  apply bv_equiv.urem, assumption, apply bvequiv_from_z,
  { cases sz, unfold_coes, simp, unfold uint_like.from_z, unfold bitvector.ne,
    unfold bitvector.of_int, simp,
    intros H, injection H, simp at h_1, rw nat.mod_pow2 at h_1,
    rw h_1 at sz_property, cases sz_property
  },
end

lemma bvequiv_never_var: ∀ sz s b,
  ¬ bv_equiv (sbitvec.var sz s) b
:= begin
  intros,intro H, cases H
end

lemma sbitvec_of_int_const: ∀ sz (b:bitvector sz),
  sbitvec.of_int sz (bitvector.to_int b) = sbitvec.const sz b
:= begin
  intros,
  cases b with b Hb,
  cases sz with sz Hsz,
  unfold_coes at *,
  unfold bitvector.to_int,
  simp,
  simp at Hb,
  have Hlt: decidable (b < 2^(sz - 1)), apply_instance,
  cases Hlt,
  {
    rw if_neg,
    unfold sbitvec.of_int,
    simp at *,
    have Hb' := nat.succ_le_of_lt Hb,
    have Hb'' := nat.sub_le_sub_right Hb' b,
    rw nat.succ_sub at Hb'',
    rw nat.sub_self at Hb'',
    generalize Hsz:2^sz - b = g,
    rw Hsz at *,
    rw nat.sub_sub,
    have Hg' : g - 1 + 1 = g,
    { rw nat.sub_add_cancel, apply Hb'' },
    rw Hg', rw ← Hsz,
    rw nat.sub_sub_self,
    rw nat.mod_eq_of_lt,
    assumption, apply le_of_lt, assumption, constructor, assumption
  },
  {
    rw if_pos,
    unfold_coes,
    unfold sbitvec.of_int,
    simp,
    rw nat.mod_eq_of_lt, assumption, assumption
  }
end

/-
 - Theorems about overflow.
 -/

lemma add_overflow_chk: ∀ (sz:size) isnsw (sa sb:sbitvec sz) (ea:bitvector sz) eb,
  bv_equiv sa ea → bv_equiv sb eb →
  b_equiv (sbitvec.overflow_chk @sbitvec.add size.one isnsw sa sb)
          (bitvector.add_overflows isnsw ea eb)
:= sorry

lemma sub_overflow_chk: ∀ (sz:size) isnsw (sa sb:sbitvec sz) (ea:bitvector sz) eb,
  bv_equiv sa ea → bv_equiv sb eb →
  b_equiv (sbitvec.overflow_chk @sbitvec.sub size.one isnsw sa sb)
          (bitvector.sub_overflows isnsw ea eb)
:= sorry

lemma mul_overflow_chk: ∀ (sz:size) isnsw (sa sb:sbitvec sz) (ea:bitvector sz) eb,
  bv_equiv sa ea → bv_equiv sb eb →
  b_equiv (sbitvec.overflow_chk @sbitvec.mul sz isnsw sa sb)
          (bitvector.mul_overflows isnsw ea eb)
:= sorry

lemma shl_overflow_chk: ∀ (sz:size) isnsw (sa sb:sbitvec sz) (ea:bitvector sz) eb,
  bv_equiv sa ea → bv_equiv sb eb →
  b_equiv (sbitvec.shl_overflow_chk sz isnsw sa sb)
          (bitvector.shl_overflows isnsw ea eb)
:= sorry


lemma to_bool_prop: ∀ p {dp:decidable p}, @to_bool p dp = tt → p
:= begin
  intros,
  cases dp,
  unfold to_bool at a, injection a
end

-- Same to poisonty_and_tt, but in the future poison may not be boolty.
lemma boolty_and_tt: ∀ (x:irsem_exec.boolty),
    bool_like.and tt x = x
:= begin intros, cases x;
  { delta bool_like.and, rw bool_is_bool_like, simp }
end

lemma boolty_or_tt2_op: ∀ (x:irsem_exec.boolty),
    x |b tt = tt
:= begin intros, cases x; refl end

lemma boolty_or_inj: ∀ {x y:irsem_exec.boolty}
    (H:bool_like.or x y = tt),
  x = tt ∨ y = tt
:= begin intros, cases x; cases y, 
  cases H,
  any_goals { right, refl },
  any_goals { left, refl }
end

lemma boolty_and_inj: ∀ {x y:irsem_exec.boolty}
    (H:bool_like.and x y = tt),
  x = tt ∧ y = tt
:= begin intros, cases x; cases y; cases H, split; simp end

@[simp]
lemma b2p_id_exec: ∀ (b:irsem_exec.boolty),
  b2p irsem_exec b = b
:= begin intros, cases b; refl end


lemma b_equiv_ite: ∀ (sb:irsem_smt.boolty) b
    (H:b_equiv sb b),
  b_equiv ((has_ite.ite sb (bool_like.tt irsem_smt.poisonty)
        (bool_like.ff irsem_smt.poisonty)):irsem_smt.poisonty) b
:= begin
  intros,
  have HB: (b = cond b tt ff), cases b; simp,
  rw HB, apply b_equiv.ite, assumption, constructor, constructor
end

lemma b_equiv_and_tt: ∀ (s1 s2:irsem_smt.boolty) b
    (H:b_equiv s1 b)
    (H':b_equiv s2 tt),
  b_equiv (bool_like.and s1 s2) b
:= begin
  intros,
  have HB: (b = band b tt),
  { cases b, simp, simp },
  rw HB, apply b_equiv.and1, assumption,
  intros H2, apply H'
end

lemma b_equiv_and_ff: ∀ (s1 s2:irsem_smt.boolty)
    (H:b_equiv s1 ff),
  b_equiv (bool_like.and s1 s2) ff
:= begin
  intros,
  have Hb': ∃ b', band ff b' = ff,
  { apply exists.intro tt, refl },
  cases Hb' with b' Hb',
  rw ← Hb',
  have Hff:(ff = bool_like.and ff b'),
  { cases b', refl, refl },
  rw Hff, apply b_equiv.and1, assumption,
  intros H0, rw ← Hff at H0, cases H0
end

lemma b_equiv_and_ff2: ∀ (s1 s2:irsem_smt.boolty)
    (H:b_equiv s2 ff),
  b_equiv (bool_like.and s1 s2) ff
:= begin
  intros,
  have Hb': ∃ b', band b' ff = ff,
  { apply exists.intro tt, refl },
  cases Hb' with b' Hb',
  rw ← Hb',
  have Hff:(ff = bool_like.and b' ff),
  { cases b', refl, refl },
  rw Hff, apply b_equiv.and2, rw ← Hff, apply H,
  intros H0, rw ← Hff at H0, cases H0
end

lemma b_equiv_and: ∀ (s1 s2:irsem_smt.boolty) (b1 b2:irsem_exec.boolty)
    (H1: b_equiv s1 b1) (H2:b_equiv s2 b2),
  b_equiv (bool_like.and s1 s2) (bool_like.and b1 b2)
:= begin
  intros,
  apply b_equiv.and1,
  assumption, cases b1, intros H, cases H, intros H, assumption
end

lemma b_equiv_or: ∀ (s1 s2:irsem_smt.boolty) (b1 b2:irsem_exec.boolty)
    (H1: b_equiv s1 b1) (H2:b_equiv s2 b2),
  b_equiv (bool_like.or s1 s2) (bool_like.or b1 b2)
:= begin
  intros,
  apply b_equiv.or1,
  assumption, cases b1, intros H, assumption, intros H, cases H
end


lemma b_equiv_never_var: ∀ s b,
  ¬ b_equiv (sbool.var s) b
:= begin
  intros,intro H, cases H
end

@[simp]
lemma poisonty_tt: irsem_exec.pbl.tt = tt
:= begin refl end

@[simp]
lemma poisonty_ff: irsem_exec.pbl.ff = ff
:= begin refl end


@[simp]
lemma poisonty_and_tt: ∀ (x:irsem_exec.poisonty),
    bool_like.and tt x = x
:= begin intros, cases x;
  { delta bool_like.and, rw bool_is_bool_like, simp }
end

lemma poisonty_and_tt_op: ∀ (x:irsem_exec.poisonty),
    tt & x = x
:= begin intros, apply poisonty_and_tt end

@[simp]
lemma poisonty_and_tt2: ∀ (x:irsem_exec.poisonty),
    bool_like.and x tt = x
:= begin intros, cases x;
  { delta bool_like.and, rw irsem_exec.pbl, rw bool_is_bool_like, simp }
end

lemma poisonty_and_tt2_op: ∀ (x:irsem_exec.poisonty),
    x & tt = x
:= begin intros, apply poisonty_and_tt2 end

lemma poisonty_and_ff: ∀ (x:irsem_exec.poisonty),
    bool_like.and ff x = ff
:= begin intros, cases x;
  { delta bool_like.and, rw bool_is_bool_like, simp }
end

lemma poisonty_and_ff_op: ∀ (x:irsem_exec.poisonty),
    ff&x = ff
:= begin intros, unfold has_and.and, apply poisonty_and_ff end

lemma poisonty_and_ff2: ∀ (x:irsem_exec.poisonty),
    bool_like.and x ff = ff
:= begin intros, cases x;
  { delta bool_like.and, rw irsem_exec.pbl, rw bool_is_bool_like, simp }
end

lemma poisonty_and_ff2_op: ∀ (x:irsem_exec.poisonty),
    x & ff = ff
:= begin intros, unfold has_and.and, apply poisonty_and_ff2 end

lemma poisonty_and_inj: ∀ {x y:irsem_exec.poisonty}
    (H:bool_like.and x y = tt),
  x = tt ∧ y = tt
:= begin intros, cases x; cases y; cases H, split; simp end

lemma poisonty_or_ff: ∀ (x:irsem_exec.poisonty),
    bool_like.or ff x = x
:= begin intros, cases x; refl end

lemma poisonty_or_ff_op: ∀ (x:irsem_exec.poisonty),
    ff |b x = x
:= begin intros, apply poisonty_or_ff end


lemma poisonty_or_inj: ∀ {x y:irsem_exec.poisonty}
    (H:bool_like.or x y = tt),
  x = tt ∨ y = tt
:= begin intros, cases x; cases y, 
  cases H,
  any_goals { right, refl },
  any_goals { left, refl }
end

lemma poison_equiv_and: forall (sx:irsem_smt.poisonty) sy
    (x:irsem_exec.poisonty) y
    (HXEQ:poison_equiv sx x)
    (HYEQ:poison_equiv sy y),
  poison_equiv (bool_like.and sx sy) (bool_like.and x y)
:= begin
  intros,
  cases HXEQ,
  cases HYEQ,
  constructor,
  apply b_equiv_and; assumption
end

lemma poison_equiv_ite: forall (sc:irsem_smt.boolty) (sx sy:irsem_smt.poisonty)
    (c:irsem_exec.boolty) (x y:irsem_exec.poisonty)
    (HCEQ:b_equiv sc c)
    (HXEQ:poison_equiv sx x)
    (HYEQ:poison_equiv sy y),
  poison_equiv (has_ite.ite sc sx sy) (has_ite.ite c x y)
:= begin
  intros,
  cases HXEQ,
  cases HYEQ,
  constructor,
  apply b_equiv.ite; assumption
end

lemma poison_equiv_and_ff: ∀ (s1 s2:irsem_smt.poisonty)
    (H:poison_equiv s1 ff),
  poison_equiv (bool_like.and s1 s2) ff
:= begin
  intros,
  cases H, constructor, apply b_equiv_and_ff, assumption
end

lemma poison_equiv_and_ff2: ∀ (s1 s2:irsem_smt.poisonty)
    (H:poison_equiv s2 ff),
  poison_equiv (bool_like.and s1 s2) ff
:= begin
  intros,
  cases H, constructor, apply b_equiv_and_ff2, assumption
end


lemma bop_poison_peel: ∀ {sz} {bopc} {flags} {ea} {eb}
    (H:bop_poison_all irsem_exec sz bopc flags ea eb = tt),
  bop_poison irsem_exec sz bopc ea eb = tt
:= begin
  unfold bop_poison_all,
  intros,
  induction flags,
  { -- when flags = []
    simp at H, assumption },
  { -- when flags = flags_hd::flags_tl
    simp at H,
    have H':= boolty_and_inj H,
    cases H', -- split ∧
    have ANSW := flags_ih H'_left,
    apply ANSW
  }
end


-- Lemmas about vppair

lemma val_equiv_eqsize: ∀ {sza szb:size}
    {a:sbitvec sza} {ap:poisonty_smt} {b bp},
  val_equiv (valty.ival sza a ap) (valty.ival szb b bp) →
  sza = szb
:= begin
  intros,
  rename a_1 H,
  cases H,
  { -- If val_equiv.poison
    assumption },
  { -- If val_equiv.concrete
    refl }
end

lemma val_equiv_eqpoison: ∀ (sza szb:size)
    (a:sbitvec sza) (ap:poisonty_smt) b bp,
  val_equiv (valty.ival sza a ap) (valty.ival szb b bp) →
  poison_equiv ap bp
:= begin
  intros,
  rename a_1 H,
  cases H; assumption
end

set_option pp.proofs true

lemma bv_equiv_cast: ∀ {sz sz':size} (sb:sbitvec sz) (bv:bitvector sz) H0 H1
    (H:bv_equiv sb bv)
    (HSZ:sz = sz'),
  @bv_equiv sz' (cast H0 sb) (cast H1 bv)
:= begin
  intros,
  induction HSZ,
  rw cast_eq,
  rw cast_eq,
  assumption
end

lemma valty_rwsize_smt: ∀ (sza szb:size) (a:irsem_smt.intty sza)
    (HSZEQ:sza = szb),
  valty.ival sza a = valty.ival szb (cast (by abstract eqH { rw HSZEQ }) a)
:= begin
  intros,
  congr,
  assumption,
  induction (valty_rwsize_smt.eqH sza szb HSZEQ),
  rw cast_eq
end

lemma valty_rwsize_exec: ∀ (sza szb:size) {a:irsem_exec.intty sza}
    (HSZEQ:sza = szb) {ap},
  valty.ival sza a ap = valty.ival szb (cast (by abstract eqH { rw HSZEQ }) a) ap
:= begin
  intros,
  congr,
  assumption,
  induction (valty_rwsize_exec.eqH sza szb HSZEQ),
  rw cast_eq
end

lemma sb_rwsize: ∀ (sza szb:size) (a:sbitvec sza)
    (HSZEQ:sza = szb),
  a = (cast (by abstract eqH {rw HSZEQ} ) a)
:= begin
  intros, rw cast_eq end

lemma bv_rwsize: ∀ (sza szb:size) (a:bitvector sza)
    (HSZEQ:sza = szb),
  a = (cast (by abstract eqH {rw HSZEQ} ) a)
:= begin
  intros, rw cast_eq end

lemma val_equiv_rwsize1: ∀ (sza sza' szb szb':size)
    (a:irsem_smt.intty sza) (b:irsem_exec.intty szb) ap bp
    (HSZEQ:sza = szb)
    (H:val_equiv (valty.ival sza a ap)
      (valty.ival sza (cast (by abstract eqH { rw HSZEQ }) b) bp)),
  val_equiv (valty.ival sza a ap) (valty.ival szb b bp)
:= begin
  intros,
  have H0: valty_rwsize_exec.eqH szb sza (eq.symm HSZEQ) =
          val_equiv_rwsize1.eqH sza szb HSZEQ, refl,
  rw ← H0 at H,
  rw ← valty_rwsize_exec at H,
  assumption
end

lemma val_equiv_rwsize2: ∀ (sza sza' szb szb':size)
    (a:irsem_smt.intty sza) (b:irsem_exec.intty szb) ap bp
    (HSZEQ1:sza = sza') (HSZEQ2:szb = szb')
    (H:val_equiv (valty.ival sza (cast (by rw HSZEQ1) a) ap)
      (valty.ival szb' (cast (by abstract eqH2 { rw HSZEQ2 }) b) bp)),
  val_equiv (valty.ival sza a ap) (valty.ival szb b bp)
:= begin
  intros,
  rw cast_eq at H,
  have H0: valty_rwsize_exec.eqH szb szb' HSZEQ2 =
          val_equiv_rwsize2.eqH2 szb szb' HSZEQ2, refl,
  rw ← H0 at H,
  rw ← valty_rwsize_exec at H,
  assumption
end

lemma val_equiv_rwsize1': ∀ (sza szb:size)
    (a:irsem_smt.intty sza) (b:irsem_exec.intty szb) ap bp
    (HSZEQ:sza = szb)
    (H:val_equiv (valty.ival sza a ap) (valty.ival szb b bp)),
  val_equiv (valty.ival sza a ap)
      (valty.ival sza (cast (by abstract eqH {rw HSZEQ}) b) bp)
:= begin
  intros, 
  have H0: valty_rwsize_exec.eqH szb sza (eq.symm HSZEQ) =
          val_equiv_rwsize1'.eqH sza szb HSZEQ, refl,
  rw ← H0,
  rw ← valty_rwsize_exec,
  assumption
end

lemma val_equiv_rwsize2': ∀ (sza sza' szb szb':size)
    (a:irsem_smt.intty sza) (b:irsem_exec.intty szb) ap bp
    (HSZEQ1:sza = sza') (HSZEQ2:szb = szb')
    (H:val_equiv (valty.ival sza a ap) (valty.ival szb b bp)),
  val_equiv (valty.ival sza' (cast (by abstract eqH1 { rw HSZEQ1 }) a) ap)
      (valty.ival szb' (cast (by abstract eqH2 { rw HSZEQ2 }) b) bp)
:= begin
  intros,
  have H0: valty_rwsize_exec.eqH szb szb' HSZEQ2 =
          val_equiv_rwsize2'.eqH2 szb szb' HSZEQ2, refl,
  have H1: valty_rwsize_smt.eqH sza sza' HSZEQ1 =
          val_equiv_rwsize2'.eqH1 sza sza' HSZEQ1, refl,
  rw ← H0,
  rw ← H1,
  rw ← valty_rwsize_exec,
  rw ← valty_rwsize_smt,
  assumption
end

lemma poison_bool_equiv: ∀ ap bp,
  poison_equiv ap bp ↔ b_equiv ap bp
:= begin
  intros,
  split,
  { intros H, cases H, assumption },
  { intros H, constructor, assumption }
end

lemma none_or_some_implies: ∀ {α β:Type} a b
    (P1 P2:α → β → Prop)
    (HP: ∀ a b, P1 a b → P2 a b)
    (H:none_or_some a b P1),
  none_or_some a b P2
:= begin
  intros,
  unfold none_or_some at *,
  cases a; cases b,  
  { left, split; refl },
  {
    cases H,
    cases H, cases H_right,
    cases H, cases H_h, cases H_h_h, cases H_h_h_left
  },
  {
    cases H,
    cases H, cases H_left,
    cases H, cases H_h, cases H_h_h, cases H_h_h_right,
    cases H_h_h_right_left
  },
  {
    cases H,
    left, apply H,
    right, cases H, cases H_h,
    apply exists.intro H_w,
    apply exists.intro H_h_w,
    cases H_h_h with H1 H2,
    cases H2 with H2 H3,
    split, assumption,
    split, assumption, apply HP, assumption
  }
end

universe u
lemma none_or_some_apply: ∀ {α β:Type} (a:α) (b:β) f, none_or_some (some a) (some b) f
  ↔ f a b
:= begin
  intros,
  unfold none_or_some,
  split,
  intros,
  cases a_1,
  cases a_1, cases a_1_left,
  cases a_1, cases a_1_h, cases a_1_h_h,
  cases a_1_h_h_left, cases a_1_h_h_right, cases a_1_h_h_right_left,
  assumption,
  intros,
  right, existsi a, existsi b, split, refl, split, refl, assumption 
end

lemma none_or_some_none: ∀ {α β:Type} {a} {b}
    {P:α → β → Prop}
    (H:none_or_some a b P)
    (H1:a = none),
  b = none
:= begin
  intros,
  subst H1,
  unfold none_or_some at H,
  cases H,
  cases H, assumption,
  cases H, cases H_h, cases H_h_h, cases H_h_h_left
end

lemma none_or_some_none2: ∀ {α β:Type} {a} {b}
    {P:α → β → Prop}
    (H1:a = none) (H2:b = none),
  none_or_some a b P
:= begin
  intros,
  subst H1, subst H2,
  unfold none_or_some,
  left, split; refl
end

lemma none_or_some_some: ∀ {α β:Type} {a} {b} {a'}
    {P:α → β → Prop}
    (H:none_or_some a b P)
    (H1:a = some a'),
  ∃ b', b = some b'
:= begin
  intros,
  subst H1,
  unfold none_or_some at H,
  cases H,
  cases H, cases H_left,
  cases H, cases H_h, cases H_h_h, cases H_h_h_right,
  apply exists.intro H_h_w, assumption
end

lemma none_or_some_false1: ∀ {α β:Type} {a:α} {f}, ¬ none_or_some (some a) (@none β) f
:= begin
  intros,
  intros H,
  unfold none_or_some at H,
  cases H, cases H, cases H_left, cases H, cases H_h,
  cases H_h_h, cases H_h_h_right, cases H_h_h_right_left
end

lemma none_or_some_false2: ∀ {α β:Type} (a:α) f, ¬ none_or_some (@none β) (some a) f
:= begin
  intros,
  intros H,
  unfold none_or_some at H,
  cases H, cases H, cases H_right, cases H, cases H_h,
  cases H_h_h, cases H_h_h_left
end

end spec
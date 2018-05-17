-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import ..smtexpr
import ..smtcompile
import ..bitvector
import .spec
import .lemmas
import .irstate
import .freevar
import .equiv
import smt2.syntax
import system.io
import init.meta.tactic
import init.meta.interactive

namespace spec

open irsem
open freevar

meta def solve_left :=
  `[ unfold freevar.env.replace_sbv,
     split, refl]

lemma foldr_and_replace: ∀ {α:Type} {f:α → poisonty_smt} p0 (l:list α) (η:freevar.env),
  η⟦list.foldr (λ itm (p:poisonty_smt), p & (f itm)) p0 l⟧ =
    list.foldr (λ itm (p:poisonty_smt), p & η⟦(f itm)⟧) (η⟦p0⟧) l
:= begin
  intros,
  induction l,
  { simp },
  {
    simp,
    rw env.replace_sb_and,
    rw ← l_ih
  }
end

lemma bop_poison_replace: ∀ sz bopc (v1 v2:sbitvec sz) (η:freevar.env),
  η⟦bop_poison irsem_smt sz bopc v1 v2⟧ =
    bop_poison irsem_smt sz bopc (η⟦v1⟧) (η⟦v2⟧)
:= begin
  intros,
  cases bopc,
  any_goals { unfold bop_poison,
    delta bop_poison._match_1, delta id_rhs,
    simp, rw env.replace_b2p, refl
  },
  any_goals { -- shl
    unfold bop_poison,
    delta bop_poison._match_1, delta id_rhs,
    simp, rw env.replace_b2p,
    try { unfold has_ult.ult, unfold has_comp.ult },
    try { unfold has_sgt.sgt, unfold has_comp.sgt },
    try { unfold has_ugt.ugt, unfold has_comp.ugt },
    unfold freevar.env.replace_sb,
    congr, unfold uint_like.from_z, rw env.replace_sbv_of_int
  }
end

lemma bop_poison_flag_replace: ∀ sz bopc (v1 v2:sbitvec sz) (η:freevar.env) flag,
  η⟦bop_poison_flag irsem_smt sz bopc flag v1 v2⟧ =
  bop_poison_flag irsem_smt sz bopc flag (η⟦v1⟧) (η⟦v2⟧)
:= begin
  intros,
  cases flag,
  any_goals { -- nsw, nuw
    unfold bop_poison_flag,
    cases bopc; unfold bop_overflow_check; rw env.replace_sb_not;
      rw env.replace_b2p,
    { unfold has_overflow_check.add_chk,
      rw env.replace_sb_overflowchk_add },
    { unfold has_overflow_check.sub_chk,
      rw env.replace_sb_overflowchk_sub },
    any_goals {
      unfold has_overflow_check.mul_chk,
      rw env.replace_sb_overflowchk_mul },
    { unfold has_overflow_check.shl_chk,
      rw env.replace_sb_overflowchk_shl }
  },
  { -- exact
    have HZERO: η⟦uint_like.zero sz⟧ = uint_like.zero sz,
    { unfold uint_like.zero, unfold sbitvec.zero, rw env.replace_sbv_of_int },
    unfold bop_poison_flag,
    cases bopc; unfold bop_exact_check; rw env.replace_sb_not; simp,
    any_goals {
      unfold bop_exact_check._match_1,
      rw env.replace_eq2p
    },
    any_goals {
      unfold has_umod.umod, unfold uint_like.urem,
      rw env.replace_sbv_urem, rw HZERO
    },
    any_goals {
      unfold has_mod.mod, unfold uint_like.srem,
      rw env.replace_sbv_srem, rw HZERO
    },
    any_goals {
      unfold has_shl.shl, unfold uint_like.shl,
      rw env.replace_sbv_shl,
      try { unfold has_lshr.lshr, unfold uint_like.lshr,
            rw env.replace_sbv_lshr },
      try { unfold has_ashr.ashr, unfold uint_like.ashr,
            rw env.replace_sbv_ashr },
      unfold has_umod.umod, unfold uint_like.urem,
      rw env.replace_sbv_urem,
      congr; unfold uint_like.from_z; rw env.replace_sbv_of_int
    }
  }
end

lemma bop_replace: ∀ sz bopc flags η v1 p1 v2 p2 ubres vres pres
    (H:(ubres, vres, pres) = bop irsem_smt sz bopc flags v1 p1 v2 p2),
  bop irsem_smt sz bopc flags (η⟦v1⟧) (η⟦p1⟧) (η⟦v2⟧) (η⟦p2⟧) =
    (η⟦ubres⟧, η⟦vres⟧, η⟦pres⟧)
:= begin
  intros,
  unfold bop at *,
  simp at *,
  injection H with HUB H,
  injection H with HV HPOISON,
  congr,
  {
    rw HUB,
    unfold bop_ub,
    cases bopc,
    any_goals { simp, refl, done }, -- non-divison ops
    any_goals { -- udiv, urem
      simp,
      rw env.replace_sb_and, rw env.replace_sb_and,
      rw env.replace_eq2p', refl,
      unfold uint_like.zero, unfold sbitvec.zero,
      rw env.replace_sbv_of_int
    },
    any_goals {
      simp,
      unfold_coes,
      unfold id,
      rw env.replace_sb_and, rw env.replace_sb_and,
      rw env.replace_sb_or, rw env.replace_sb_and,
      rw env.replace_eq2p',
      rw env.replace_eq2p',
      rw env.replace_eq2p',
      { unfold uint_like.allone, unfold sbitvec.uintmax, rw env.replace_sbv_of_int },
      { unfold uint_like.signonly, unfold sbitvec.intmin, rw env.replace_sbv_of_int },
      { unfold uint_like.zero, unfold sbitvec.zero, rw env.replace_sbv_of_int }
    }
  },
  {
    rw HV,
    cases bopc,
    { unfold bop_val,
      unfold has_add.add, unfold uint_like.add, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_sub.sub, unfold uint_like.sub, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_mul.mul, unfold uint_like.mul, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_udiv.udiv, unfold uint_like.udiv, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_umod.umod, unfold uint_like.urem, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_div.div, unfold uint_like.sdiv, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_mod.mod, unfold uint_like.srem, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_and.and, unfold uint_like.and, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_or.or, unfold uint_like.or, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_xor.xor, unfold uint_like.xor, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_shl.shl, unfold uint_like.shl, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_lshr.lshr, unfold uint_like.lshr, unfold freevar.env.replace_sbv },
    { unfold bop_val,
      unfold has_ashr.ashr, unfold uint_like.ashr, unfold freevar.env.replace_sbv }
  },
  {
    rw HPOISON,
    unfold bop_poison_all,
    rw env.replace_sb_and, rw env.replace_sb_and,
    have AND:∀ (p1 p2 q1 q2:poisonty_smt),
      p1&p2 = q1&q2 ↔ p1 = q1 ∧ p2 = q2,
    {
      intros,
      split,
      {
        unfold has_and.and, unfold bool_like.and,
        intros H,
        injection H, split; assumption
      },
      { intros H, cases H with H1 H2, rw [H1, H2] }
    },
    rw AND, rw AND,
    split,
    {
      rw foldr_and_replace,
      rw bop_poison_replace,
      apply list.foldr_eq; try { refl },
      { intros, rw AND, split, refl,
        rw bop_poison_flag_replace },
    },
    split ; refl
  }
end

lemma replace_to_ival: ∀ {sz:size} (v:intty_smt sz) (p:poisonty_smt) (η:freevar.env),
  η⟦to_ival irsem_smt (v, p)⟧ = to_ival irsem_smt (η⟦v⟧, η⟦p⟧)
:= begin
  intros,
  unfold to_ival,
  unfold freevar.env.replace_valty
end

lemma step_bop_replace: ∀ (ss:irstate_smt) bopc flags
    (vop1 vop2: valty_smt)
    vop1' vop2' (η:freevar.env) lhsn
    (HVOP1:vop1' = η⟦vop1⟧)
    (HVOP2:vop2' = η⟦vop2⟧),
  step_bop irsem_smt vop1' vop2' bopc flags (η⟦ss⟧) lhsn =
    η⟦step_bop irsem_smt vop1 vop2 bopc flags ss lhsn⟧'
:= begin
  intros,
  cases vop1 with sz1 v1 p1,
  cases vop2 with sz2 v2 p2,
  unfold freevar.env.replace_valty at *,
  rw [HVOP1, HVOP2],
  unfold step_bop,
  have HSZ: decidable(sz1 = sz2), apply_instance,
  cases HSZ,
  { -- sz1 ≠ sz2
    rw dif_neg, rw dif_neg, assumption, assumption },
  { -- sz1 = sz2
    rw dif_pos, rw dif_pos,
    have HTY: sbitvec sz2 = irsem_smt.intty sz1,
    { rw HSZ, refl },
    generalize HRES1: bop irsem_smt sz1 bopc flags
        (η⟦v1⟧) (η⟦p1⟧) (cast HTY (η⟦v2⟧)) (η⟦p2⟧) = res1,
    generalize HRES2: (bop irsem_smt sz1 bopc flags
        v1 p1 (cast HTY v2) p2) = res2,
    cases res1 with resub1 resvp1,
    cases resvp1 with resv1 resp1,
    cases res2 with resub2 resvp2,
    cases resvp2 with resv2 resp2,
    unfold step_bop._match_2,
    unfold apply,
    rw replace_updatereg,
    rw replace_updateub,
    rw ← env.replace_sbv_cast at HRES1,
    rw bop_replace at HRES1,
    injection HRES1,
    injection h_2 with h_2 h_3,
    congr,
    rw h_1, rw replace_to_ival, congr, rw h_2, rw h_3,
    rw HRES2, repeat { rw HSZ }
  }
end

lemma icmpop_replace: ∀ sz cond η v1 p1 v2 p2 vres pres
    (H:(vres, pres) = icmpop irsem_smt sz cond v1 p1 v2 p2),
  icmpop irsem_smt sz cond (η⟦v1⟧) (η⟦p1⟧) (η⟦v2⟧) (η⟦p2⟧) = (η⟦vres⟧, η⟦pres⟧)
:= begin
  intros,
  cases cond,
  all_goals {
    unfold icmpop at *,
    simp at *,
    unfold icmpop._match_1 at *,
    injection H,
    rw h_1,
    rw h_2,
    rw env.replace_sb_and,
    unfold_coes,
    rw env.replace_sbv_of_bool,
    unfold_ops
  },
  { rw env.replace_sb_eqbv },
  { rw env.replace_sb_nebv },
  { rw env.replace_sb_ult },
  { rw env.replace_sb_ule },
  { rw env.replace_sb_ult },
  { rw env.replace_sb_ule },
  { rw env.replace_sb_slt },
  { rw env.replace_sb_sle },
  { rw env.replace_sb_slt },
  { rw env.replace_sb_sle }
end

lemma step_icmpop_replace: ∀ (ss:irstate_smt) cond
    (vop1 vop2: valty_smt)
    vop1' vop2' (η:freevar.env) lhsn
    (HVOP1:vop1' = η⟦vop1⟧)
    (HVOP2:vop2' = η⟦vop2⟧),
  step_icmpop irsem_smt vop1' vop2' cond (η⟦ss⟧) lhsn =
    η⟦step_icmpop irsem_smt vop1 vop2 cond ss lhsn⟧'
:= begin
  intros,
  cases vop1 with sz1 v1 p1,
  cases vop2 with sz2 v2 p2,
  unfold freevar.env.replace_valty at *,
  rw [HVOP1, HVOP2],
  unfold step_icmpop,
  have HSZ: decidable(sz1 = sz2), apply_instance,
  cases HSZ,
  { -- sz1 ≠ sz2
    rw dif_neg, rw dif_neg, assumption, assumption },
  { -- sz1 = sz2
    rw dif_pos, rw dif_pos,
    have HTY: sbitvec sz2 = irsem_smt.intty sz1,
    { rw HSZ, refl },
    generalize HRES1: icmpop irsem_smt sz1 cond (η⟦v1⟧) (η⟦p1⟧)
        (cast HTY (η⟦v2⟧)) (η⟦p2⟧) = res1,
    generalize HRES2: (icmpop irsem_smt sz1 cond v1 p1
        (cast HTY v2) p2) = res2,
    cases res1 with resv1 resp1,
    cases res2 with resv2 resp2,
    unfold apply,
    rw replace_updatereg,
    rw ← env.replace_sbv_cast at HRES1,
    rw icmpop_replace at HRES1,
    injection HRES1,
    congr,
    rw replace_to_ival, rw h_1, rw h_2,
    rw HRES2, repeat { rw HSZ }
  }
end

lemma selectop_replace: ∀ sz η vcond pcond v1 p1 v2 p2 vres pres
    (H:(vres, pres) = selectop irsem_smt vcond pcond sz v1 p1 v2 p2),
  selectop irsem_smt (η⟦vcond⟧) (η⟦pcond⟧) sz (η⟦v1⟧) (η⟦p1⟧) (η⟦v2⟧) (η⟦p2⟧)
    = (η⟦vres⟧, η⟦pres⟧)
:= begin
  intros,
  unfold selectop at *,
  simp at *,
  injection H,
  rw [h_1, h_2],
  unfold has_ite.ite,
  unfold has_eq.eq, unfold has_comp.eq,
  congr,
  {
    rw env.replace_sbv_ite,
    rw env.replace_sb_eqbv,
    congr
  },
  {
    rw env.replace_sb_and,
    rw env.replace_sb_ite,
    rw env.replace_sb_eqbv,
    congr
  }
end

lemma step_selectop_replace: ∀ (ss:irstate_smt)
    (vcond vop1 vop2: valty_smt)
    vcond' vop1' vop2' (η:freevar.env) lhsn
    (HVCOND:vcond' = η⟦vcond⟧)
    (HVOP1:vop1' = η⟦vop1⟧)
    (HVOP2:vop2' = η⟦vop2⟧),
  step_selectop irsem_smt vcond' vop1' vop2' (η⟦ss⟧) lhsn =
    η⟦step_selectop irsem_smt vcond vop1 vop2 ss lhsn⟧'
:= begin
  intros,
  cases vcond with szcond vcond pcond,
  cases vop1 with sz1 v1 p1,
  cases vop2 with sz2 v2 p2,
  unfold freevar.env.replace_valty at *,
  rw [HVCOND, HVOP1, HVOP2],
  unfold step_selectop,
  have HSZ: decidable(szcond = size.one), apply_instance,
  cases HSZ,
  { -- szcond != size.one
    rw dif_neg, rw dif_neg, assumption, assumption
  },
  { -- szcond = size.one
    rw dif_pos, rw dif_pos HSZ,
    have HSZ2: decidable(sz1 = sz2), apply_instance,
    cases HSZ2,
    {
      rw dif_neg, rw dif_neg, assumption, assumption
    },
    {
      rw dif_pos, rw dif_pos,
      rw ← env.replace_sbv_cast,
      rw ← env.replace_sbv_cast,
      unfold apply,
      rw replace_updatereg,
      rw selectop_replace,
      { congr },
      { refl },
      any_goals { assumption },
      rw HSZ2
    }
  }
end

lemma castop_replace: ∀ fromsz code op1 op1p tosz η vres pres
    (H:(vres, pres) = castop irsem_smt fromsz code op1 op1p tosz),
  castop irsem_smt fromsz code (η⟦op1⟧) (η⟦op1p⟧) tosz
    = (η⟦vres⟧, η⟦pres⟧)
:= begin
  intros,
  cases code,
  any_goals {
    unfold castop at *,
    have H1: decidable (fromsz.val < tosz.val), apply_instance,
    have H2: decidable (fromsz.val = tosz.val), apply_instance,
    cases H1,
    {
      rw if_neg at *, any_goals { assumption },
      cases H2,
      {
        rw if_neg at *, any_goals { assumption },
        injection H with h_1 h_2, rw h_1, rw h_2,
        congr,
        unfold uint_like.trunc, rw env.replace_sbv_trunc
      },
      {
        rw if_pos at *, any_goals { assumption },
        injection H with h_1 h_2, rw h_1, rw h_2,
        congr, unfold uint_like.zero, unfold sbitvec.zero,
        rw env.replace_sbv_of_int
      }
    },
    {
      rw if_pos at *, any_goals { assumption },
      injection H with h_1 h_2, rw h_1, rw h_2,
      try { unfold uint_like.sext, rw env.replace_sbv_sext },
      try { unfold uint_like.zext, rw env.replace_sbv_zext },
    }
  }
end

lemma step_unaryop_replace: ∀ (ss:irstate_smt)
    (vop:valty_smt) (code:uopcode) (toisz:nat) vop' (η:freevar.env) lhsn
    (HVOP:vop' = η⟦vop⟧),
  step_unaryop irsem_smt vop' code toisz (η⟦ss⟧) lhsn =
    η⟦step_unaryop irsem_smt vop code toisz ss lhsn⟧'
:= begin
  intros,
  cases vop with sz v p,
  unfold freevar.env.replace_valty at *,
  rw HVOP,
  cases code,
  { unfold step_unaryop },
  all_goals { unfold step_unaryop,
    have HSZ: decidable (toisz > 0), apply_instance,
    cases HSZ,
    {
      rw dif_neg, rw dif_neg, assumption, assumption
    },
    {
      rw dif_pos, rw dif_pos,
      simp,
      unfold apply,
      rw replace_updatereg,
      rw castop_replace,
      { congr },
      { simp },
      { assumption }
    }
  }
end

lemma step_replace: ∀ (ss:irstate_smt) (i:instruction)
    (η:freevar.env),
  step_exe irsem_smt (η⟦ss⟧) i = η⟦step_exe irsem_smt ss i⟧'
:= begin
  intros,
  cases i,
  case instruction.binop : retty lhs bopc flags op1 op2 {
    cases lhs,

    unfold step_exe,
    unfold has_bind.bind,
    rw get_value_replace,
    generalize HOP1: η⟦get_value irsem_smt ss op1 retty⟧' = vop1,
    generalize HOP2: η⟦get_value irsem_smt ss op2 retty⟧' = vop2,
    simp at HOP1,
    cases vop1,
    { -- none
      rw apply_none at HOP1, rw HOP1, unfold option.bind
    },
    {
      have HOP1' := apply_some HOP1,
      cases HOP1' with vop1' HOP1',
      rw HOP1',
      rw get_value_replace,
      simp at HOP2,
      cases vop2,
      { -- none
        rw apply_none at HOP2, rw HOP2,
        unfold option.bind,
      },
      {
        have HOP2' := apply_some HOP2,
        cases HOP2' with vop2' HOP2',
        rw HOP2',
        unfold option.bind,
        rw step_bop_replace,
        {
          rw HOP1' at HOP1, unfold apply at HOP1, injection HOP1, rw h_1
        },
        { rw HOP2' at HOP2 }
      }
    }
  },
  case instruction.icmpop : opty lhs cond op1 op2 {
    cases lhs,
    
    unfold step_exe,
    unfold has_bind.bind,
    rw get_value_replace,
    generalize HOP1: η⟦get_value irsem_smt ss op1 opty⟧' = vop1,
    generalize HOP2: η⟦get_value irsem_smt ss op2 opty⟧' = vop2,
    simp at HOP1,
    cases vop1,
    { -- none
      rw apply_none at HOP1, rw HOP1, unfold option.bind
    },
    {
      have HOP1' := apply_some HOP1,
      cases HOP1' with vop1' HOP1',
      rw HOP1',
      rw get_value_replace,
      simp at HOP2,
      cases vop2,
      { -- none
        rw apply_none at HOP2, rw HOP2,
        unfold option.bind,
      },
      {
        have HOP2' := apply_some HOP2,
        cases HOP2' with vop2' HOP2',
        rw HOP2',
        unfold option.bind,
        rw step_icmpop_replace,
        {
          rw HOP1' at HOP1, unfold apply at HOP1, injection HOP1, rw h_1
        },
        { rw HOP2' at HOP2 }
      }
    }
  },
  case instruction.selectop : lhs condty cond opty op1 op2 {
    cases lhs,
    
    unfold step_exe,
    unfold has_bind.bind,
    rw get_value_replace,

    generalize HOPCOND: η⟦get_value irsem_smt ss cond condty⟧' = vopcond,
    generalize HOP1: η⟦get_value irsem_smt ss op1 opty⟧' = vop1,
    generalize HOP2: η⟦get_value irsem_smt ss op2 opty⟧' = vop2,
    simp at *,
    cases vopcond,
    { rw apply_none at HOPCOND, rw HOPCOND, unfold option.bind },
    {
      have HOPCOND' := apply_some HOPCOND,
      cases HOPCOND' with vopcond' HOPCOND',
      rw HOPCOND',
      rw get_value_replace,
      unfold option.bind,
      
      cases vop1,
      { rw apply_none at HOP1, rw HOP1, unfold option.bind },
      {
        have HOP1' := apply_some HOP1,
        cases HOP1' with vop1' HOP1',
        rw HOP1',
        rw get_value_replace,
        unfold option.bind,

        cases vop2,
        { rw apply_none at HOP2, rw HOP2, unfold option.bind },
        {
          have HOP2' := apply_some HOP2,
          cases HOP2' with vop2' HOP2',
          rw HOP2',
          unfold option.bind,
          rw step_selectop_replace,
          { rw HOPCOND' at HOPCOND, unfold apply at HOPCOND, injection HOPCOND,
            rw h_1 },
          { rw HOP1' at HOP1 },
          { rw HOP2' at HOP2 }
        }
      }
    }
  },
  case instruction.unaryop : lhs ucode fromty op toty {
    cases lhs,
    cases toty,
    {
      unfold step_exe,
      unfold has_bind.bind,
      rw get_value_replace,

      generalize HOP: η⟦get_value irsem_smt ss op fromty⟧' = vop,
      simp at *,
      cases vop,
      { unfold option.bind, rw apply_none at HOP, rw HOP, refl },
      {
        have HOP' := apply_some HOP,
        cases HOP' with vop' HOP',
        rw HOP',
        unfold option.bind,
        rw step_unaryop_replace,
        { rw HOP' at HOP, unfold apply at HOP, injection HOP, rw h_1 }
      }
    },
    {
      unfold step_exe
    }
  }
end

theorem step_encode_both: ∀ ss se i oss ose η
    (HENC:encode ss se η)
    (HOSS': oss = step_exe irsem_smt ss i)
    (HOSE': ose = step_exe irsem_exec se i),
  none_or_some oss ose (λ ss' se', encode ss' se' η)
:= begin
  intros,
  have HSTEP : none_or_some (step_exe irsem_smt (η⟦ss⟧) i)
      (step_exe irsem_exec se i) (λ ss' se', irstate_equiv ss' se'),
  {
    apply step_both_prf,
    apply HENC,
    refl, refl
  },
  have HOSS'': η⟦oss⟧' = step_exe irsem_smt (η⟦ss⟧) i, {
    rw step_replace,
    rw HOSS'
  },
  simp at HOSS'',
  rw ← HOSS'' at *,
  rw ← HOSE' at *,
  unfold encode at *,
  cases oss,
  {
    unfold none_or_some at *,
    cases HSTEP,
    { rw apply_none at HSTEP, left, assumption },
    { cases HSTEP with _ HSTEP,
      cases HSTEP with _ HSTEP,
      cases HSTEP with HSTEP _,
      unfold apply at HSTEP,
      cases HSTEP
    }
  },
  {
    unfold none_or_some at *,
    cases HSTEP,
    {
      left, cases HSTEP with HSTEP _,
      cases HSTEP
    },
    {
      unfold apply at HSTEP,
      cases HSTEP with s HSTEP,
      cases HSTEP with e HSTEP,
      cases HSTEP with HSTEP_l HSTEP,
      cases HSTEP with HSTEP_r HSTEP_r2,
      injection HSTEP_l,
      rw ← h_1 at HSTEP_r2,
      right,
      apply exists.intro oss,
      apply exists.intro e,
      split, refl,
      split, assumption,
      assumption
    }
  }
end


theorem bigstep_both_prf: bigstep_both
:= begin
  unfold bigstep_both,
  intros,
  revert ss se oss' ose',
  cases p,
  induction p with i p',
  { -- empty instruction
    intros,
    unfold irsem.bigstep_exe at HOSS' HOSE',
    simp at HOSS' HOSE',
    right,
    apply exists.intro ss,
    apply exists.intro se,
    split, assumption, split, assumption, assumption
  },
  { -- a new instruction at the front
    intros,
    generalize HSS:irsem.step_exe irsem_smt ss i = oss0,
    generalize HSE:irsem.step_exe irsem_exec se i = ose0,
    have HENC0 : none_or_some oss0 ose0 (λ ss0 se0, encode ss0 se0 η),
    {
      apply step_encode_both,
      apply HENC, rw HSS, rw HSE
    },
    cases oss0,
    { -- none, none
      have H: ose0 = none, {
        apply none_or_some_none,
        apply HENC0, refl
      },
      rw H at *,
      rw bigstep_unroll_none_smt at HOSS',
      rw bigstep_unroll_none_exec at HOSE',
      rw HOSS', rw HOSE',
      apply none_or_some_none2; refl,
      rw HSE, rw HSS
    },
    { -- some, some
      have H: (∃ se0', ose0 = some se0'), {
        apply none_or_some_some,
        apply HENC0, refl
      },
      cases H with se0' H,
      rw H at *,
      unfold none_or_some at HENC0,
      cases HENC0,
      {
        cases HENC0, cases HENC0_left
      },
      {
        cases HENC0 with s HENC0,
        cases HENC0 with e HENC0,
        cases HENC0 with _ HENC0,
        cases HENC0 with _ HENC0,
        apply p_ih,
        apply HENC0,
        rw ← bigstep_unroll_some_smt, apply HOSS', rw HSS, rw HENC0_left,
        rw ← bigstep_unroll_some_exec, apply HOSE', rw HSE, rw HENC0_left_1
      }
    }
  }
end

lemma bigstep_replace: ∀ ss p (η:freevar.env),
  η⟦bigstep_exe irsem_smt ss p⟧' = bigstep_exe irsem_smt (η⟦ss⟧) p
:= begin
  intros,
  simp,
  cases p,
  revert ss,
  induction p with i p,
  {
    intros,
    refl
  },
  {
    intros,
    generalize HSS: step_exe irsem_smt ss i = ss',
    generalize HRSS: step_exe irsem_smt (η⟦ss⟧) i = rss',
    cases ss'; cases rss',
    {
      rw bigstep_unroll_none_smt,
      rw bigstep_unroll_none_smt,
      rw HRSS, rw HSS
    },
    any_goals {
      rw step_replace at HRSS,
      rw HSS at HRSS, cases HRSS, done
    },
    {
      rw bigstep_unroll_some_smt,
      rw bigstep_unroll_some_smt,
      apply p_ih,
      have HTMP: η⟦step_exe irsem_smt ss i⟧' = η⟦some ss'⟧',
      {
        rw HSS
      },
      rw ← step_replace at HTMP, rw HRSS at HTMP,
      unfold apply at HTMP, injection HTMP,
      rw h_1 at HRSS,
      apply (eq.symm HRSS),
      rw HSS
    }
  }
end

end spec
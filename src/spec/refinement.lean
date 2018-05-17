-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import ..smtexpr
import ..smtcompile
import ..bitvector
import ..verifyopt
import .spec
import .lemmas
import .irstate
import .freevar
import .equiv
import .openprog
import ..irsem_exec
import smt2.syntax
import system.io
import init.meta.tactic
import init.meta.interactive

namespace spec

open opt
open irsem

set_option pp.proofs true
lemma check_val_exec_spec_prf : check_val_exec_spec
:= begin
  unfold check_val_exec_spec,
  intros,
  cases vsrc with szsrc vsrc psrc,
  cases vtgt with sztgt vtgt ptgt,
  unfold check_val at H,
  have HSZ:decidable (sztgt = szsrc), apply_instance,
  cases HSZ,
  { rw dif_neg at H, cases H, apply neq_symm, assumption },
  {
    rw dif_pos at H,
    rw valty_rwsize_exec sztgt szsrc,
    injection H with H,
    generalize H0: (vsrc =_{irsem_exec.boolty}
      cast (check_val._match_1._proof_1
        irsem_exec szsrc sztgt (eq.symm HSZ)) vtgt) = t,
    rw H0 at H,
    unfold has_not.not at H,
    unfold has_or.or at H,
    unfold has_and.and at H,

    cases psrc,
    {
      apply val_refines.poison_intty, refl
    },
    {
      apply val_refines.concrete_intty,
      { refl },
      { cases ptgt,
        {
          cases t, cases H, cases H
        },
        refl },
      {
        cases t,
        { cases ptgt, cases H, cases H },
        {
          unfold has_eq.eq at H0,
          unfold has_comp.eq at H0,
          unfold bitvector.eq at H0,
          simp at H0, rw H0
        }
      }
    },
    any_goals { assumption }
  }
end



set_option pp.proofs true
lemma check_val_replace: ∀ vssrc vstgt (η:freevar.env),
  η⟦opt.check_val irsem_smt vssrc vstgt⟧' = opt.check_val irsem_smt (η⟦vssrc⟧) (η⟦vstgt⟧)
:= begin
  intros,
  cases vssrc, cases vstgt,
  unfold opt.check_val,
  unfold freevar.env.replace_valty,
  have HSZ: decidable (vssrc_sz = vstgt_sz), apply_instance,
  cases HSZ,
  {
    unfold check_val._match_1,
    rw dif_neg HSZ,
    rw dif_neg HSZ
  },
  {
    unfold check_val._match_1,
    rw dif_pos HSZ,
    rw dif_pos HSZ,
    unfold apply,
    unfold_coes,
    unfold id,
    rw env.replace_sb_or,
    rw env.replace_sb_not,
    rw env.replace_sb_and,
    unfold has_eq.eq, unfold has_comp.eq,
    rw env.replace_sb_eqbv,
    rw env.replace_sbv_cast, rw HSZ
  }
end

lemma check_val_some: ∀ {vssrc vstgt vesrc vetgt sres eres}
    (HEQS:equals_size vssrc vesrc = tt)
    (HEQT:equals_size vstgt vetgt = tt)
    (HS:sres = opt.check_val irsem_smt vssrc vstgt)
    (HE:eres = opt.check_val irsem_exec vesrc vetgt),
  none_or_some sres eres (λ s e, true)
:= begin
  intros,
  cases vssrc, cases vesrc, cases vstgt, cases vetgt,
  unfold equals_size at HEQS, simp at HEQS,
  unfold equals_size at HEQT, simp at HEQT,
  unfold check_val at HS,
  unfold check_val at HE,

  have HSZ': decidable (vssrc_sz = vstgt_sz), apply_instance,
  cases HSZ',
  {
    have HSZ'': vesrc_sz ≠ vetgt_sz,
    { rw ← HEQS, rw ← HEQT, assumption },
    rw dif_neg HSZ' at HS,
    rw dif_neg HSZ'' at HE,
    unfold none_or_some, left, split; assumption
  },
  {
    have HSZ'': vesrc_sz = vetgt_sz,
    { rw ← HEQS, rw ← HEQT, assumption },
    rw dif_pos HSZ' at HS,
    rw dif_pos HSZ'' at HE,
    cases sres, cases HS, injection HS,
    cases eres, cases HE, injection HE,
    unfold none_or_some, right, apply exists.intro,
    apply exists.intro, split, refl, split, refl, constructor
  }
end

lemma check_val_equiv: ∀ {vssrc vstgt vesrc vetgt sres eres}
    (HEQS:val_equiv vssrc vesrc)
    (HEQT:val_equiv vstgt vetgt)
    (HS:sres = opt.check_val irsem_smt vssrc vstgt)
    (HE:eres = opt.check_val irsem_exec vesrc vetgt),
  none_or_some sres eres (λ s e, b_equiv s e)
:= begin
  intros,
  cases vssrc, cases vstgt,
  cases vesrc, cases vetgt, -- make ivals
  have HSSZEQ := val_equiv_eqsize HEQS,
  have HTSZEQ := val_equiv_eqsize HEQT,
  unfold opt.check_val at *,

  have HSZ': decidable (vssrc_sz = vstgt_sz), apply_instance,
  cases HSZ',
  {
    have HSZ'': vesrc_sz ≠ vetgt_sz,
    {
      rw ← HSSZEQ, rw ← HTSZEQ, assumption
    },
    rw dif_neg HSZ' at HS,
    rw dif_neg HSZ'' at HE,
    rw HS, rw HE, unfold none_or_some, left, split;refl
  },
  {
    have HSZ'': vesrc_sz = vetgt_sz,
    { rw [← HSSZEQ, ← HTSZEQ], rw HSZ' },
    rw dif_pos HSZ' at HS,
    rw dif_pos HSZ'' at HE,
    cases sres, cases HS,
    cases eres, cases HE,
    injection HS with HS, injection HE with HE,
    unfold none_or_some,
    right,
    existsi sres, existsi eres,
    split, refl, split, refl,
    rw [HS, HE],

    cases HEQS,
    { -- source is poison.
      cases HEQS_a with HEQS_a,
      apply b_equiv.or1,
      { apply b_equiv.not, unfold_coes, unfold id, assumption },
      { intros H, rw HEQS_a_2 at H, cases H }
    },
    { -- source is concrete value,
      cases HEQS_a,
      cases HEQT,
      { -- target is poison
        apply b_equiv.or1, apply b_equiv.not, assumption,
        intros, apply b_equiv.and1, cases HEQT_a, assumption,
        intros, rw HEQT_a_2 at a_1, cases a_1
      },
      {
        cases HEQT_a,
        apply b_equiv.or1,
        { apply b_equiv.not, assumption },
        { intros, apply b_equiv.and1, assumption, intros,
          apply b_equiv.eq, assumption, --apply HEQT_a_1, apply bv_equiv.cast,
          apply bv_equiv_cast, assumption, rw HSZ''
        }
      }
    }
  }
end


universe u
lemma check_single_reg0_replace: ∀ psrc ptgt root ss0 (η:freevar.env),
    η⟦opt.check_single_reg0 irsem_smt psrc ptgt root ss0⟧' =
        opt.check_single_reg0 irsem_smt psrc ptgt root (η⟦ss0⟧)
:= begin
  intros,
  unfold opt.check_single_reg0,
  generalize HSS: irsem.bigstep_exe irsem_smt ss0 psrc = oss,
  generalize HSS': irsem.bigstep_exe irsem_smt ss0 ptgt = oss',
  rw ← bigstep_replace,
  rw ← bigstep_replace,
  rw HSS, rw HSS',
  unfold has_bind.bind,
  cases oss; cases oss';unfold option.bind,
  generalize HSV: irstate.getreg irsem_smt oss root = ovs,
  generalize HSV': irstate.getreg irsem_smt oss' root = ovs',
  rw getreg_replace HSV,
  rw getreg_replace HSV',
  cases ovs; cases ovs'; unfold option.bind,
  rw ← check_val_replace,
  generalize HCV: check_val irsem_smt ovs ovs' = ocv,
  cases ocv;unfold option.bind,
  unfold return, unfold pure,
  unfold apply,
  rw env.replace_sb_or,
  rw env.replace_sb_not,
  rw replace_getub,
  rw env.replace_sb_and,
  rw replace_getub
end

lemma check_single_reg0_equiv: ∀ psrc ptgt root ss0 se0 sres eres
    (HEQ:irstate_equiv ss0 se0)
    (HS:sres = opt.check_single_reg0 irsem_smt psrc ptgt root ss0)
    (HE:eres = opt.check_single_reg0 irsem_exec psrc ptgt root se0)
    (HEQS:irstate_equiv ss0 se0),
  none_or_some sres eres (λ s e, b_equiv s e)
:= begin
  intros,
  unfold opt.check_single_reg0 at *,
  unfold has_bind.bind at HS,
  unfold has_bind.bind at HE,
  generalize HSS: irsem.bigstep_exe irsem_smt ss0 psrc = oss,
  generalize HSS': irsem.bigstep_exe irsem_smt ss0 ptgt = oss',
  generalize HSE: irsem.bigstep_exe irsem_exec se0 psrc = ose,
  generalize HSE': irsem.bigstep_exe irsem_exec se0 ptgt = ose',
  rw [HSS, HSS'] at HS,
  rw [HSE, HSE'] at HE,
  have HPTGT_ENTANGLED: none_or_some oss' ose' (λ ss' se', irstate_equiv ss' se'),
  {
    apply bigstep_both_equiv,
    assumption, rw HSS', rw HSE'
  },
  have HPSRC_ENTANGLED: none_or_some oss ose (λ ss' se', irstate_equiv ss' se'),
  {
    apply bigstep_both_equiv,
    assumption, rw HSS, rw HSE
  },
  cases oss; cases oss';
  cases ose; cases ose',
  any_goals { unfold option.bind at HS, unfold option.bind at HE,
              rw HS, rw HE, unfold none_or_some, left, split; refl },
  any_goals {
    exfalso, apply none_or_some_false2, apply HPSRC_ENTANGLED
  },
  any_goals {
    exfalso, apply none_or_some_false1, apply HPSRC_ENTANGLED
  },
  any_goals {
    exfalso, apply none_or_some_false2, apply HPTGT_ENTANGLED
  },
  any_goals {
    exfalso, apply none_or_some_false1, apply HPTGT_ENTANGLED
  },
  rw none_or_some_apply at HPSRC_ENTANGLED,
  rw none_or_some_apply at HPTGT_ENTANGLED,
  unfold option.bind at HS,
  unfold option.bind at HE,
  generalize HSV: irstate.getreg irsem_smt oss root = ovs,
  generalize HSV': irstate.getreg irsem_smt oss' root = ovs',
  generalize HEV: irstate.getreg irsem_exec ose root = ove,
  generalize HEV': irstate.getreg irsem_exec ose' root = ove',
  have HSRCVEQ := irstate.getreg_equiv HPSRC_ENTANGLED (eq.symm HSV) (eq.symm HEV),
  have HTGTVEQ := irstate.getreg_equiv HPTGT_ENTANGLED (eq.symm HSV') (eq.symm HEV'),
  rw [HSV, HSV'] at HS,
  rw [HEV, HEV'] at HE,
  cases ovs; cases ovs'; cases ove; cases ove',
  any_goals { unfold option.bind at HS, unfold option.bind at HE,
              rw HS, rw HE, unfold none_or_some, left, split; refl },
  any_goals {
    exfalso, apply none_or_some_false2, apply HSRCVEQ
  },
  any_goals {
    exfalso, apply none_or_some_false1, apply HSRCVEQ
  },
  any_goals {
    exfalso, apply none_or_some_false2, apply HTGTVEQ
  },
  any_goals {
    exfalso, apply none_or_some_false1, apply HTGTVEQ
  },
  rw none_or_some_apply at HSRCVEQ,
  rw none_or_some_apply at HTGTVEQ,
  unfold option.bind at HS,
  unfold option.bind at HE,
  cases HSRCVEQ with HSRCSZEQ HSRCVEQ,
  cases HTGTVEQ with HTGTSZEQ HTGTVEQ,
  generalize HSCV: check_val irsem_smt ovs ovs' = scv,
  generalize HECV: check_val irsem_exec ove ove' = ecv,
  rw HSCV at HS, rw HECV at HE,
  have HCVRET := check_val_some HSRCSZEQ HTGTSZEQ (eq.symm HSCV) (eq.symm HECV),
  cases scv ; cases ecv,
  { unfold option.bind at HS, unfold option.bind at HE,
    rw HS, rw HE, unfold none_or_some, left, split; refl },
  {
    unfold option.bind at HS,
    unfold option.bind at HE,
    exfalso, apply none_or_some_false2,
    assumption
  },
  {
    unfold option.bind at HS,
    unfold option.bind at HE,
    exfalso, apply none_or_some_false1,
    assumption
  },
  unfold option.bind at HS,
  unfold option.bind at HE,
  unfold return at *, unfold pure at *,
  unfold none_or_some, right,
  apply exists.intro,
  apply exists.intro,
  split, assumption,
  split, assumption,
  generalize HUB: (~irstate.getub irsem_exec ose) = ub,
  cases ub,
  {
    apply b_equiv.or1,
    {
      rw ← HUB, apply b_equiv.not,
      apply irstate.getub_equiv,
      apply HPSRC_ENTANGLED,
      refl, refl
    },
    {
      generalize HUB': irstate.getub irsem_exec ose' = ub',
      cases ub',
      {
        intros, apply b_equiv.and1,
        rw ← HUB',
        apply irstate.getub_equiv,
        apply HPTGT_ENTANGLED, refl, rw HUB', intros Q, cases Q
      },
      {
        intros, apply b_equiv.and1,
        apply irstate.getub_equiv,
        apply HPTGT_ENTANGLED, refl, rw HUB',
        have HNOUB: has_no_ub ose = tt,
        {
          cases ose, unfold irstate.getub at HUB,
          simp at HUB, unfold has_not.not at HUB,
          cases ose_fst, cases HUB, refl
        },
        have HNOUB': has_no_ub ose' = tt,
        {
          cases ose', unfold irstate.getub at HUB',
          simp at HUB',
          cases ose'_fst, cases HUB', refl
        },
        have HV := HSRCVEQ HNOUB,
        have HV' := HTGTVEQ HNOUB',
        have HCVRET := check_val_equiv HV HV' (eq.symm HSCV) (eq.symm HECV),
        rw none_or_some_apply at HCVRET,
        intros, assumption
      }
    }
  },
  {
    apply b_equiv.or1,
    {
      rw ← HUB, apply b_equiv.not, apply irstate.getub_equiv, apply HPSRC_ENTANGLED,
      refl, refl
    },
    {
      intros Q, cases Q
    }
  }
end


theorem refines_single_reg_correct_prf: refines_single_reg_correct
:= begin
  unfold refines_single_reg_correct,
  intros,
  unfold root_refines_smt,
  intros,
  unfold root_refines_finalstate,
  intros,
  generalize HEREF: check_single_reg0 irsem_exec psrc ptgt root se0 = oeb,
  have HSREF': some (η⟦sb⟧) = check_single_reg0 irsem_smt psrc ptgt root (η⟦ss0⟧),
  {
    rw ← check_single_reg0_replace,
    rw ← HSREF
  },
  have HCHKEQ: none_or_some (some (η⟦sb⟧)) oeb (λ s e, b_equiv s e),
  {
    apply check_single_reg0_equiv,
    unfold encode at a, apply a,
    rw HSREF', rw HEREF, unfold encode at a, apply a
  },
  cases oeb with eb,
  { exfalso, apply none_or_some_false1, assumption },
  rw none_or_some_apply at HCHKEQ,
  have HCHKTT := HEQ η eb HCHKEQ,
  
  unfold root_refines,
  unfold check_single_reg0 at HEREF,
  rw [← a_1, ← a_2] at HEREF,
  unfold has_bind.bind at HEREF,
  unfold option.bind at HEREF,
  generalize HV: (irstate.getreg irsem_exec se root) = ov,
  generalize HV': (irstate.getreg irsem_exec se' root) = ov',
  rw [HV, HV'] at HEREF,
  cases ov with v; cases ov' with v',
  any_goals { unfold option.bind at HEREF, cases HEREF, done },
  unfold option.bind at HEREF,

  generalize HCV: check_val irsem_exec v v' = ocv,
  rw HCV at HEREF,
  cases ocv with cv,
  any_goals { unfold option.bind at HEREF, cases HEREF, done },
  unfold option.bind at HEREF,
  injection HEREF with HEREF,
  subst HCHKTT,
  split,
  {
    generalize HUBSRC : irstate.getub irsem_exec se = ubsrc,
    generalize HUBTGT : irstate.getub irsem_exec se' = ubtgt,
    rw HUBSRC at HEREF,
    rw HUBTGT at HEREF,
    cases ubsrc,
    {
      apply ub_refines.ub,
      rw HUBSRC, refl
    },
    {
      apply ub_refines.noub, rw HUBSRC, refl,
      cases ubtgt,
      { cases cv; cases HEREF },
      { rw HUBTGT, refl }
    }
  },
  {
    intros HUBTRUE,
    existsi v, existsi v',
    split, refl, split, refl,
    apply check_val_exec_spec_prf,
    rw HUBTRUE at HEREF,
    cases (irstate.getub irsem_exec se'); cases cv,
    any_goals { cases HEREF, done },
    assumption
  }
end

end spec
-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import ..smtexpr
import ..smtcompile
import ..bitvector
import .spec
import .lemmas
import .lemmas_basic
import .irstate
import .freevar
import .equiv
import .closed
import smt2.syntax
import system.io
import init.meta.tactic
import init.meta.interactive

namespace spec

open irsem
open freevar

-- get_free_*_name

lemma get_free_name_diff: ∀ n,
  get_free_sbitvec_name n ≠ get_free_sbool_name n
:= begin
  intros,
  intros H,
  unfold get_free_sbitvec_name at H,
  unfold get_free_sbool_name at H,
  rw string.eq_list at H,
  rw string.append_to_list at H,
  rw string.append_to_list at H,
  have H' := list.append_eq2 H,
  cases H'
end


lemma closed_regfile_apply_add_b_bv: ∀ (rf:regfile irsem_smt) (η:freevar.env)
    vname vz bname vb
    (HC:closed_regfile (rf.apply_to_values irsem_smt (env.replace_valty η))),
  closed_regfile (rf.apply_to_values irsem_smt
      (env.replace_valty ((η.add_bv vname vz).add_b bname vb)))
:= begin
  intros,
  revert HC,
  apply regfile.induction rf,
  {
    unfold closed_regfile,
    intros,
    rw regfile.empty_apply_empty,
    apply closed_regfile_empty
  },
  {
    intros rf IH,
    intros,
    unfold closed_regfile,
    intros,
    rw regfile.apply_update_comm at HC,
    rw regfile.apply_update_comm,
    unfold closed_regfile at IH,
    rw closed_regfile_update_split at HC,
    cases HC with HC HCval,
    have HC := IH HC,
    rw closed_regfile_update_split,
    split,
    {
      assumption
    },
    {
      cases v,
      unfold freevar.env.replace_valty at HCval,
      rw closed_ival_split at HCval,
      cases HCval with HCval1 HCval2,
      unfold freevar.env.replace_valty,
      rw closed_ival_split,
      split,
      {
        have H := closed_b_add_bv vname vz HCval1,
        have H := closed_b_add_b bname vb H,
        assumption
      },
      {
        have H := closed_bv_add_bv vname vz HCval2,
        have H := closed_bv_add_b bname vb H,
        assumption
      }
    }
  }
end

lemma regfile_update_ival_closed: ∀ rf rf' (η:freevar.env) regn sz
    vn pn bvn p
    (HCRF: closed_regfile (regfile.apply_to_values irsem_smt rf
           (env.replace_valty η)))
    (HRF': rf' = regfile.update irsem_smt rf regn
           (valty.ival sz (sbitvec.var sz vn) (sbool.var pn))),
  closed_regfile (regfile.apply_to_values irsem_smt rf'
    (env.replace_valty (env.add_b (env.add_bv η vn bvn) pn p)))
:= begin
  intros,
  have H1 : closed_regfile (regfile.apply_to_values irsem_smt
            rf (env.replace_valty (env.add_b (env.add_bv η vn bvn) pn p))),
  {
    apply closed_regfile_apply_add_b_bv,
    assumption
  },
  have H2 : closed_valty
            ((env.add_b (env.add_bv η vn bvn) pn p)
              ⟦valty.ival sz (sbitvec.var sz vn) (sbool.var pn)⟧),
  { apply ival_closed },
  rw HRF',
  rw regfile.apply_update_comm,
  rw closed_regfile_update_split,
  split, assumption, assumption
end

lemma updatereg_closed: ∀ (ss ss':irstate_smt) (η:freevar.env)
    regn sz vn pn bvn p
    (HC:closed_irstate (η⟦ss⟧))
    (HNOTIN1: vn ∉ η)
    (HNOTIN2: pn ∉ η)
    (HNOTEQ: vn ≠ pn)
    (HS:ss' = irstate.updatereg irsem_smt ss regn
        (irsem.valty.ival sz (sbitvec.var sz vn) (sbool.var pn))),
  closed_irstate (((η.add_bv vn bvn).add_b pn p)⟦ss'⟧)
:= begin
  intros,
  cases ss with sub srf,
  cases ss' with sub' srf',
  unfold freevar.env.replace at *,
  rw ← irstate.setub_apply_to_values at *,
  unfold irstate.getub at *,
  simp at *,
  unfold irstate.setub at *,
  unfold irstate.apply_to_values at *,
  rw closed_irstate_split,
  rw closed_irstate_split at HC,
  cases HC with HCUB HCRF,
  unfold irstate.updatereg at HS,
  simp at *,
  injection HS,
  subst h_1,
  split,
  {
    have H0: closed_b ((env.add_bv η vn bvn)⟦sub'⟧),
    {
      apply closed_b_add_bv,
      apply HCUB
    },
    apply closed_b_add_b,
    { assumption }
  },
  {
    apply regfile_update_ival_closed, assumption, assumption
  }
end

-- encode


-- Note that `irstate_equiv η⟦iss⟧ ise` does not imply
-- closed_irstate η⟦iss⟧. It is because, for example,
-- `b_equiv (sbool.and (sbool.var _) (sbool.ff)) ff` holds.
-- Then why `encode iss ise` is needed? -> encode is
-- the only way to relate ise and iss.
lemma init_var_encode_intty: ∀ ise iss ise' iss' (sg sg':std_gen) η n t
    (HENC: encode iss ise η) (HCLOSED: closed_irstate (η⟦iss⟧))
    (HNOTIN1: get_free_sbitvec_name n ∉ η)
    (HNOTIN2: get_free_sbool_name n ∉ η)
    (HIE:(ise', sg') = create_init_var_exec n t (ise, sg))
    (HIS:iss' = create_init_var_smt n t iss),
  ∃ η', (encode iss' ise' η' ∧ closed_irstate (η'⟦iss'⟧) ∧
         env.added2 η (get_free_sbitvec_name n)
          (get_free_sbool_name n) η')
:= begin
  intros,
  
  unfold create_init_var_smt at HIS,
  simp at HIS,

  unfold create_init_var_exec at HIE,
  simp at HIE,
  generalize Hrbv':(get_rand_bv (get_sz_from_ty t) sg) = rbv',
  cases rbv' with rbv' sg'',
  rw Hrbv' at *,
  unfold create_init_var_exec._match_2 at HIE,
  generalize Hrb':(get_rand_bool sg'') = rb',
  cases rb' with rb' sg''',
  rw Hrb' at *,
  unfold create_init_var_exec._match_1 at HIE,
  injection HIE with HIE HIE_sg,
  simp at HIE,

  existsi ((η.add_b (get_free_sbool_name n) rb')
             .add_bv (get_free_sbitvec_name n) rbv'.to_int),
  split,
  {
    unfold encode,
    rw HIS,
    rw replace_updatereg,
    rw HIE,
    rw env.not_in_add_bv_irstate_comm,
    rw env.not_in_add_b_irstate_comm,
    rw HCLOSED, rw HCLOSED,
    rw env.not_in_add_bv_valty_comm,
    rw env.not_in_add_b_valty_comm,

    unfold freevar.env.replace_valty,
    -- making value..
    unfold get_free_sbitvec,
    rw env.not_in_replace_sbv,
    rw env.add_b_replace_sbv,
    rw env.empty_replace_sbv,
    rw env.add_bv_replace_match,
    -- making poison..
    unfold get_free_sbool,
    rw env.not_in_replace_sb,
    rw env.add_b_replace_match,
    rw env.replace_sb_of_bool,
    apply irstate.updatereg_equiv,
    {
      intros,
      cases rb',
      { -- poison
        apply val_equiv.poison_intty,
        { constructor, constructor },
        { refl },
        { refl }
      },
      {
        apply val_equiv.concrete_intty,
        { constructor, constructor },
        {
          cases rbv',
          rw sbitvec_of_int_const,
          constructor
        },
        { refl }
      }
    },
    { rw sbitvec_of_int_const, unfold equals_size, simp },
    { apply HENC },
    any_goals { assumption },
    any_goals {
      apply env.not_in_add_b,
      apply get_free_name_diff,
      assumption
    },
  },
  split,
  {
    unfold closed_irstate,
    intros,
    rw HIS,
    rw replace_updatereg,
    rw env.not_in_add_bv_irstate_comm,
    rw env.not_in_add_b_irstate_comm,
    rw HCLOSED, rw HCLOSED,
    rw env.not_in_add_bv_valty_comm,
    rw env.not_in_add_b_valty_comm,

    unfold freevar.env.replace_valty,
    -- making value..
    unfold get_free_sbitvec,
    rw env.not_in_replace_sbv,
    rw env.add_b_replace_sbv,
    rw env.empty_replace_sbv,
    rw env.add_bv_replace_match,
    -- making poison..
    unfold get_free_sbool,
    rw env.not_in_replace_sb,
    rw env.add_b_replace_match,
    rw env.replace_sb_of_bool,

    rw replace_updatereg,
    unfold freevar.env.replace_valty,
    rw env.replace_sbv_of_int,
    rw env.replace_sb_of_bool,
    rw HCLOSED,
    any_goals { assumption },
    apply env.not_in_add_b, apply get_free_name_diff, assumption,
    apply env.not_in_add_b, apply get_free_name_diff, assumption
  },
  {
    unfold env.added2,
    split, {
      intros n_1 H1 H2,
      cases H2,
      apply env.not_in_add_bv,
      assumption,
      apply env.not_in_add_b,
      assumption,
      rw env.not_in_split at H1,
      rw env.not_in_split,
      assumption
    },
    {
      intros n_1 H,
      unfold env.add_b,
      unfold env.add_bv,
      unfold has_mem.mem, simp,
      cases H,
      {
        rw if_neg, rw if_neg, unfold has_mem.mem at H,
        cases H, left, assumption, right, assumption,
        intros H', rw H' at H, apply HNOTIN1, assumption,
        intros H', rw H' at H, apply HNOTIN2, assumption,
      },
      {
        cases H,
        { right, rw if_pos, intros H0, cases H0, assumption },
        { left, rw if_pos, intros H0, cases H0, assumption }
      }
    }
  }
end

def fv_smt_names (fvnames:list string) :=
  fvnames.map get_free_sbitvec_name ++
    fvnames.map get_free_sbool_name

lemma init_state_encode_strong: ∀ (freevars:list (string × ty)) (sg sg':std_gen) ise iss
    (HUNQ: list.unique $ freevars.map prod.fst)
    (HIE:(ise, sg') = create_init_state_exec freevars sg)
    (HIS:iss = create_init_state_smt freevars),
  ∃ η, (encode iss ise η ∧ closed_irstate (η⟦iss⟧)
      ∧ env.has_only η (fv_smt_names $ freevars.map prod.fst))
:= begin
  intros,
  revert ise iss sg sg',
  induction freevars,
  {
    intros,
    unfold create_init_state_exec at HIE,
    unfold create_init_state_smt at HIS,
    simp at HIE,simp at HIS,
    injection HIE with HIE _,
    rw [HIS, HIE],
    existsi (freevar.env.empty),
    unfold encode, rw empty_replace_st,
    constructor, constructor, constructor,
    any_goals { constructor },
    {
      apply closed_irstate_empty
    },
    {
      unfold fv_smt_names, simp,
      unfold env.has_only, intros, split,
      { intros H, cases H },
      { intros H, have H := (env.not_in_empty name) H, cases H }
    }
  },
  {
    intros,
    rename freevars_tl tl,
    cases freevars_hd with vname vty,
    have HEtmp: ∀ h t, create_init_state_exec (h::t) sg
              = create_init_var_exec h.1 h.2 (create_init_state_exec t sg),
    { intros, refl },
    rw HEtmp at HIE,
    clear HEtmp,
    have HStmp: ∀ h t, create_init_state_smt (h::t)
              = create_init_var_smt h.1 h.2 (create_init_state_smt t),
    { intros, refl },
    rw HStmp at HIS,
    clear HStmp,
    generalize HE0: create_init_state_exec tl sg = ise_sg0,
    generalize HS0: create_init_state_smt tl = iss0,
    rw HE0 at *,
    rw HS0 at *,
    cases ise_sg0 with ise0 sg0,
    simp at HIE HIS,
    have HEX: (∃ (η0 : env), encode iss0 ise0 η0 ∧ closed_irstate (η0⟦iss0⟧)
                ∧ env.has_only η0 (fv_smt_names $ tl.map prod.fst)),
    {
      apply freevars_ih,
      {
        simp at HUNQ, cases HUNQ, assumption
      }, apply (eq.symm HE0), refl
    },
    cases HEX with η0 HEX,
    cases HEX with HEX1 HEX2,
    cases HEX2 with HEX2 HEX3,
    -- Now add a new variable to each irstate
    have HUPDATED: ∃ η', (encode iss ise η' ∧ closed_irstate (η'⟦iss⟧) ∧
         env.added2 η0 (get_free_sbitvec_name vname)
                            (get_free_sbool_name vname) η'),
    {
      apply init_var_encode_intty,
      apply HEX1,
      apply HEX2,
      { -- get_free_sbitvec_name vname ∉ η0
        simp at HUNQ, cases HUNQ,
        apply env.has_only_not_in,
        { apply HEX3 },
        { unfold fv_smt_names,
          unfold get_free_sbitvec_name,
          apply list.not_mem_append,
          apply slist_prefix_notin, assumption,
          apply slist_prefix_notin2 "v_" "b_" 'v' 'b', assumption,
          { intros H0, cases H0 }, refl, refl
        }
      },
      { -- get_free_sbool_name vname ∉ η0
        simp at HUNQ, cases HUNQ,
        apply env.has_only_not_in,
        { apply HEX3 },
        { unfold fv_smt_names,
          unfold get_free_sbool_name,
          apply list.not_mem_append,
          apply slist_prefix_notin2 "b_" "v_" 'b' 'v', assumption,
          { intros H0, cases H0 }, refl, refl,
          apply slist_prefix_notin, assumption,
        }
      },
      assumption, assumption
    },
    cases HUPDATED with η HUPDATED,
    cases HUPDATED with HUPDATED Htmp, -- env.has_only_added2 (Honly) (Hadd2)
    cases Htmp with HUPDATED2 HUPDATED3,
    have Hη := env.has_only_added2 HEX3 HUPDATED3,
    existsi η,
    split, assumption, split, assumption,
    {
      unfold fv_smt_names, simp,
      unfold fv_smt_names at Hη, simp at Hη,
      rw ← list.cons_append,
      rw ← env.has_only_shuffle (get_free_sbool_name vname),
      simp,
      rw env.has_only_shuffle2,
      apply Hη
    }
  }
end

theorem init_state_encode_prf: init_state_encode
:= begin
  unfold init_state_encode,
  intros,
  have H := init_state_encode_strong freevars sg sg' ise iss HUNQ
            HIE HIS,
  cases H with η H,
  cases H, existsi η, assumption
end

-- Future work: theorem that `freevars.get` correctly returns all
-- free variables.

end spec
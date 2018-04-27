import ..smtexpr
import ..smtcompile
import ..bitvector
import .spec
import .lemmas
import .irstate
import smt2.syntax
import system.io
import init.meta.tactic
import init.meta.interactive

namespace spec

open smt

lemma bitvec_zero_add: ∀ sz (b1 b2:bitvector sz),
  b1.val = 0 → bitvector.add b1 b2 = b2 :=
begin
  intros sz b1 b2 H,
  apply subtype.eq, unfold bitvector.add, simp, unfold_coes,
  rw H, simp, rw nat.mod_eq_of_lt,
  apply b2.property
end

-- THE MAIN THEOREM.
lemma optimize_add_zero_sound:
  ∀ (sz:size) (s:sbitvec sz) b, bv_equiv s b → bv_equiv (optimize_add_zero s) b
:= begin
  intros sz s b H,
  cases H,
  { -- bv_equiv.const
    rw sbitvec_cons_notoptimized, constructor },
  { -- bv_equiv.add
    cases H_s1,
    { 
      cases H_s1_n,
      { unfold optimize_add_zero at *, simp at *,
        cases H_b1,
        cases H_b1_val,
        { rw ← bitvector.add, rw bitvec_zero_add, assumption, simp },
        { cases H_a }
      },
      { apply bv_equiv.add; assumption }
    },
    all_goals { apply bv_equiv.add; assumption }
  },
  all_goals { -- for all remaining goals..
    constructor; assumption
  }
end

open irsem

/-
 - regfile_sametypes
 -/

lemma regfile.equiv_sametypes: ∀ rs re
    (H:regfile_equiv rs re),
  regfile_sametypes rs re
:= begin
  intros,
  induction H,
  {
    rw H_a, rw H_a_1,
    unfold regfile_sametypes,
    intros,
    rw regfile.empty_get_none at a,
    rw regfile.empty_get_none at a,
    left, assumption
  },
  {
    rw H_a_2, rw H_a_3,
    unfold regfile_sametypes,
    intros,
    cases a,
    have HDEC: decidable (rname = H_rname), apply_instance,
    cases HDEC,
    {
      rw regfile.update_get_nomatch at a_left,
      rw regfile.update_get_nomatch at a_right,
      apply H_ih,
      { split; assumption },
      assumption, assumption
    },
    {
      rw regfile.update_get_match at a_left,
      rw regfile.update_get_match at a_right,
      right,
      apply exists.intro H_vs,
      apply exists.intro H_ve,
      split, assumption, split, assumption,
      {
        cases H_vs, cases H_ve, simp,
        apply val_equiv_eqsize,
        assumption
      },
      assumption, assumption
    }
  }
end

lemma regfile.sametypes_update: ∀ rs re (rname:string)
    (sv:valty_smt) (ev:valty_exec)
    (H:regfile_sametypes rs re)
    (HV:equals_size sv ev = tt),
  regfile_sametypes (regfile.update irsem_smt rs rname sv)
                    (regfile.update irsem_exec re rname ev)
:= begin
  intros,
  unfold regfile_sametypes,
  intros,
  have HDEC:decidable (rname = rname_1), apply_instance,
  cases HDEC,
  {
    rw regfile.update_get_nomatch at a,
    rw regfile.update_get_nomatch at a,
    { apply H, assumption },
    any_goals { intros HDEC', apply HDEC, rw HDEC' }
  },
  {
    right,
    rw regfile.update_get_match at a,
    rw regfile.update_get_match at a,
    {
      cases a, --split and
      apply (exists.intro sv),
      apply (exists.intro ev),
      split, assumption,
      split, assumption,
      assumption
    },
    rw HDEC, rw HDEC
  }
end

/-
 - irstate_equiv
 -/

lemma irstate.updateub_equiv: ∀ (ss:irstate_smt) (se:irstate_exec) sb eb
    (HEQ:irstate_equiv ss se)
    (HBEQ:b_equiv sb eb),
  irstate_equiv (irstate.updateub irsem_smt ss sb)
                (irstate.updateub irsem_exec se eb)
:= begin
  intros,
  unfold irstate.updateub at *, -- reveal pairs
  cases HEQ,
  { -- irstate.noub
    simp,
    cases eb,
    { -- eb = ff
      apply irstate_equiv.ub,
      apply b_equiv_and, assumption, assumption,
      cases HEQ_ube; try {refl},
      cases HEQ,
      { apply regfile.equiv_sametypes, assumption },
      { assumption }
    },{ -- eb = tt
      apply irstate_equiv.noub,
      assumption,
      apply b_equiv_and, assumption, assumption, rw HEQ_a_2, refl
    }
  },{ -- irstate.ub
    apply irstate_equiv.ub,
    apply b_equiv_and, simp, assumption, assumption,
    { rw HEQ_a_1, simp, cases eb; refl },
    apply HEQ_a_2
  }
end

lemma irstate.updatereg_equiv: ∀ (ss:irstate_smt) (se:irstate_exec) name sv ev
    (HVEQ:has_no_ub se = tt → val_equiv sv ev)
    (HSZEQ: equals_size sv ev = tt)
    (HEQ:irstate_equiv ss se),
  irstate_equiv (irstate.updatereg irsem_smt ss name sv)
                (irstate.updatereg irsem_exec se name ev)
:= begin
  intros,
  cases ss, cases se,
  unfold irstate.updatereg at *, -- reveal pairs
  simp,
  cases HEQ,
  { -- irstate_equiv.noub
    apply irstate_equiv.noub,
    { -- equiv. of register file
      unfold regfile.update,
      apply regfile_equiv.update,
      assumption, apply HVEQ, assumption,
      unfold regfile.update, unfold regfile.update
    },
    { -- equiv. of UB
      assumption },
    { assumption }
  },
  { -- irstate_equiv.ub
    -- regfiles may differ.
    apply irstate_equiv.ub, assumption, assumption,
    apply regfile.sametypes_update, assumption,
    assumption
  }
end


/-
 - Theorems about irstate.
 -/

-- If two irstates are equivalent, doing regfile.get both return none,
-- or return values which are equivalent.
lemma irstate.getreg_equiv: ∀ {ss:irstate_smt} {se:irstate_exec} {rname:string}
    {sret} {eret} (HSTEQ:irstate_equiv ss se)
    (HSSRET: sret = ss.getreg irsem_smt rname)
    (HSERET: eret = se.getreg irsem_exec rname),
  none_or_some sret eret
    (λ sretv eretv, equals_size sretv eretv = tt
      ∧ (has_no_ub se = tt → val_equiv sretv eretv))
:= begin
  intros,
  cases HSTEQ,
  { -- irstate_equiv.noub
    rename HSTEQ_a_1 HUBEQ,
    rename HSTEQ_a HREGEQ,
    clear HUBEQ, -- UB in the state is not needed,
    induction HREGEQ,
    { -- when regfile is empty
      rw HREGEQ_a at *,
      rw HREGEQ_a_1 at *,
      unfold irstate.getreg at *,
      simp [regfile.empty_get_none] at *,
      left, split; assumption
    },
    { -- There are two cases:
      -- (1) The register updated doesn't equal to rname.
      -- (2) The register previously updated has the name 'rname'
      have Helper_str: (decidable_eq string), apply_instance,
      cases (Helper_str rname HREGEQ_rname),
      { -- The case (1)
        rw HREGEQ_a_2 at HSSRET,
        rw HREGEQ_a_3 at HSERET,
        unfold irstate.getreg at *,
        -- HSTEQ_a_rname should be filtered out.
        rw regfile.update_get_nomatch at HSSRET; try {assumption},
        rw regfile.update_get_nomatch at HSERET; try {assumption},
        -- Now use induction hypothesis!!
        simp at HREGEQ_ih,
        apply HREGEQ_ih,
        -- A. Using the previous (not-updated) register file is enough
        { assumption }, -- in SMT
        { assumption }, -- in Exec. semantics
        { -- B. Show irstate_equiv before the register update.
          constructor,
          { assumption },
          -- How do we get b_equiv HSTEQ_ubs HSTEQ_ube?
          -- regfile.update does not change UB state, so we can infer it.
          { cases HSTEQ, assumption, assumption },
          { assumption } }
      },
      { -- The case (2)
        -- we don't need induction hypothesis here.
        clear HREGEQ_ih,
        rename HREGEQ_vs vs,
        rename HREGEQ_ve ve,
        -- Let's start!
        rw HREGEQ_a_2  at HSSRET HSTEQ,
        rw HREGEQ_a_3  at HSERET HSTEQ,
        unfold irstate.getreg at *,
        simp at HSSRET HSERET,
        rw regfile.update_get_match at HSERET; try {assumption},
        rw regfile.update_get_match at HSSRET; try {assumption},
        -- There exists concrete value!
        right,
        existsi [vs, ve],
        split, assumption, split, assumption,
        cases vs, -- destruct valty into ival
        cases ve, 
        -- val_equiv HSTEQ_a_vs HSTEQ_a_ve ∧ poison_equiv HSTEQ_a_ps HSTEQ_a_pe
        cases HSTEQ,
        cases HSTEQ_a,
        { injection HSTEQ_a_a }, -- regfile cannot be empty because it is just updated,
        { unfold regfile.update at *, injection HSTEQ_a_a_2,
          split, {
            unfold equals_size, simp, apply val_equiv_eqsize,
            assumption
          },
          { injection h_1 } },
        { split,
          { simp, apply val_equiv_eqsize, assumption },
          { intros, assumption }
        },
      }
    }
  }, { -- irstate_equiv.ub
    unfold irstate.getreg at HSSRET HSERET,
    simp at HSSRET HSERET,
    unfold regfile_sametypes at HSTEQ_a_2,

    have HSTEQ' := HSTEQ_a_2 rname sret eret (and.intro HSSRET HSERET),
    clear HSTEQ_a_2,
    cases HSTEQ',
    {
      left, assumption
    },
    {
      cases HSTEQ' with vs HSTEQ',
      cases HSTEQ' with ve HSTEQ',
      cases HSTEQ' with HSTEQ'1 HSTEQ'2,
      cases HSTEQ'2 with HSTEQ'2 HSTEQ'3,
      right,
      apply exists.intro vs,
      apply exists.intro ve,
      split, assumption,
      split, assumption,
      split, assumption,
      intros H, rw HSTEQ_a_1 at H, cases H
    }
  }
end

/-
 - Theorems about get_value
 -/

lemma get_value_equiv: ∀ ss es sv ev op retty
    (HSTEQ: irstate_equiv ss es)
    (HSV:sv = get_value irsem_smt ss op retty)
    (HEV:ev = get_value irsem_exec es op retty),
  (sv = none ∧ ev = none) ∨
  (∃ sv' ev', sv = some sv' ∧ ev = some ev' ∧
      equals_size sv' ev' = tt ∧
      (has_no_ub es = tt → val_equiv sv' ev'))
:= begin
  intros,
  cases op,
  { -- when the operand is register
    cases op,
    unfold get_value at *,
    apply irstate.getreg_equiv; assumption
  },
  { -- when the operand is constant
    cases op,
    cases retty,
    { -- type of the register is isz
      unfold get_value at *,
      have H: (decidable (0 < retty)), apply_instance,
      cases H,
      { -- if sz <= 0, get_value returns none.
        simp [H] at *, left, split; assumption
      },
      {
        simp [H] at HSV HEV,
        have HRANGE: (decidable (within_signed_range ⟨retty, _⟩ op)), {
          unfold within_signed_range,
          simp, apply_instance 
        },
        cases HRANGE,
        {
          simp [HRANGE] at HSV HEV,
          have HRANGE2: (decidable (↑(int_min_nat ⟨retty, _⟩) ≤ op ∧ op ≤ ↑(all_one_nat ⟨retty, _⟩))), {
            unfold int_min_nat, unfold all_one_nat, unfold_coes, simp,
            apply_instance
          },
          cases HRANGE2,
          { simp [HRANGE2] at HSV HEV, left, split; assumption },
          { simp [HRANGE2] at HSV HEV, right,
            apply exists.intro,
            apply exists.intro,
            split,
            apply HSV, split, apply HEV,
            split,
            { -- equals_size
              simp },
            { -- if no ub, val_equiv
              intros HUB,
              apply val_equiv.concrete_intty,
              { apply poison_equiv.intro, apply b_equiv.tt },
              { unfold uint_like.from_z,
                apply bvequiv_of_int
              }, simp
            }
          }, assumption, assumption
        },
        {
          simp [HRANGE] at HSV HEV,
          right,
          apply exists.intro,
          apply exists.intro,
          split, apply HSV, split, apply HEV,
          split, simp,
          intros HUB,
          apply val_equiv.concrete_intty,
            constructor, constructor,
            unfold uint_like.from_z,
            apply bvequiv_of_int, constructor
        }, assumption
      }
    },
    { -- ty_int.arbitrary_int
      unfold get_value at *,
      left, split;assumption
    }
  }
end

-- specialized version of get_value_equiv
lemma get_value_none: ∀ ss es sv op retty
    (HSTEQ: irstate_equiv ss es)
    (HSV:sv = get_value irsem_smt ss op retty)
    (HEV:none = get_value irsem_exec es op retty),
  sv = none
:= begin
  intros,
  have H:= get_value_equiv ss es sv none op retty HSTEQ HSV HEV,
  cases H,
  { cases H, assumption },
  { -- cannot happen. guide to exfalso
    cases H with _ H _,
    cases H with _ H _,
    cases H with _ H _,
    cases H with H _ _,
    cases H
  }
end

lemma get_value_some: ∀ ss es sv (ev':valty_exec) op retty
    (HSTEQ: irstate_equiv ss es)
    (HSV:sv = get_value irsem_smt ss op retty)
    (HEV:some ev' = get_value irsem_exec es op retty),
  (∃ sv', sv = some sv' ∧
      equals_size sv' ev' = tt ∧
      (has_no_ub es = tt → val_equiv sv' ev'))
:= begin
  intros,
  have H:= get_value_equiv ss es sv (some ev') op retty HSTEQ HSV HEV,
  cases H,
  { cases H, cases H_right }, -- exfalso
  {
    cases H with sv' H _,
    cases H with ev'' H _,
    cases H with H1 H2,
    cases H2 with H21 H22,
    cases H22 with H22 H23,
    injection H21, rw h_1 at *,
    apply exists.intro sv',
    split, assumption, split, assumption, assumption
  }
end

/-
 - Theorems about select operation.
 -/

lemma selectop_equiv_true: ∀ (ss:irstate_smt) (se:irstate_exec) (szs sze:size)
    scond scondp (econd:irsem_exec.intty size.one) econdp
    (sa:sbitvec szs) sap sb sbp (ea:bitvector sze) eap
    (eb:bitvector sze) ebp sres sresp eres eresp
    (HSTEQ:irstate_equiv ss se)
    (HCONDONE:econd = uint_like.from_z size.one 1 ∧ econdp = tt)
    (HCONDEQ:poison_equiv scondp econdp ∧ bv_equiv scond econd)
    (HAEQ:val_equiv (irsem.valty.ival szs sa sap)
                       (irsem.valty.ival sze ea eap))
    (HBEQ:val_equiv (irsem.valty.ival szs sb sbp)
                       (irsem.valty.ival sze eb ebp))
    (HSZEQ:szs = sze)
    (HSRES: (sres,sresp) = selectop irsem_smt scond scondp szs sa sap sb sbp)
    (HERES: (eres,eresp) = selectop irsem_exec econd econdp sze ea eap eb ebp),
  val_equiv (irsem.valty.ival szs sres sresp) (irsem.valty.ival sze ea eap)
:= begin
  intros,
  cases HCONDONE with HCONDONE1 HCONDONE2,
  cases HCONDEQ with HCONDP HCOND,
  unfold selectop at *,
  simp at *,
  injection HSRES with HSRES HSRESP,
  injection HERES with HERES HERESP,
  cases HAEQ,
  { -- poison
    apply val_equiv.poison_intty,
    {
      rw HSRESP,
      have H:eap = eresp, {
        rw HERESP,
        rw HCONDONE2,
        rw HCONDONE1,
        unfold has_eq.eq, simp, unfold bitvector.eq, cases eap; refl
      },
      rw H,
      rw HERESP,
      apply poison_equiv_and, 
      { assumption },
      {
        constructor,
        apply b_equiv.ite,
        { apply b_equiv.eq, assumption, constructor },
        { cases HAEQ_a, assumption },
        { cases HBEQ; cases HBEQ_a; assumption }
      }
    },
    any_goals { assumption }
  },
  { -- not poison
    apply val_equiv.concrete_intty,
    {
      have H:eap = eresp, {
        rw HERESP,
        rw HCONDONE2,
        rw HCONDONE1,
        unfold has_eq.eq, simp, unfold bitvector.eq, cases eap; refl
      },
      rw H,
      rw HERESP, rw HSRESP,
      apply poison_equiv_and,
      { assumption },
      { constructor,
        apply b_equiv.ite,
        { apply b_equiv.eq, assumption, constructor },
        { cases HAEQ_a, assumption },
        { cases HBEQ; cases HBEQ_a; assumption }
      }
    },
    {
      have H:HAEQ_ve = eres, {
        rw HERES,
        rw HCONDONE1,
        unfold has_eq.eq, simp, unfold bitvector.eq, cases eap; refl
      },
      rw H,
      rw HERES, rw HSRES,
      apply bv_equiv.ite,
      {
        apply b_equiv.eq, assumption, constructor
      }, {
        intros, assumption
      }, {
        cases HBEQ,
        any_goals { -- operand2 is either poison or concrete,
          -- but cond is tt, so operand2 is never used!
          intros H, rw HCONDONE1 at H,
          unfold has_eq.eq at H, simp at H, unfold bitvector.eq at H,
          cases H
        }
      }
    },
    assumption
  }
end

lemma selectop_equiv_false: ∀ (ss:irstate_smt) (se:irstate_exec) (szs sze:size)
    scond scondp (econd:bitvector size.one) econdp (sa:sbitvec szs) sap sb sbp (ea:bitvector sze) eap
    (eb:bitvector sze) ebp sres sresp eres eresp
    (HSTEQ:irstate_equiv ss se)
    (HCONDZERO:econd ≠ uint_like.from_z size.one 1 ∧ econdp = tt)
    (HCONDEQ:poison_equiv scondp econdp ∧ bv_equiv scond econd)
    (HAEQ:val_equiv (irsem.valty.ival szs sa sap)
                       (irsem.valty.ival sze ea eap))
    (HBEQ:val_equiv (irsem.valty.ival szs sb sbp)
                       (irsem.valty.ival sze eb ebp))
    (HSZEQ:szs = sze)
    (HSRES: (sres,sresp) = selectop irsem_smt scond scondp szs sa sap sb sbp)
    (HERES: (eres,eresp) = selectop irsem_exec econd econdp sze ea eap eb ebp),
  val_equiv (irsem.valty.ival szs sres sresp) (irsem.valty.ival sze eb ebp)
:= begin
  intros,
  cases HCONDZERO with HCONDZERO1 HCONDZERO2,
  cases HCONDEQ with HCONDP HCOND,
  unfold selectop at *,
  simp at *,
  injection HSRES with HSRES HSRESP,
  injection HERES with HERES HERESP,
  cases HBEQ,
  { -- operand 2 is poison
    apply val_equiv.poison_intty,
    {
      rw HSRESP,
      have H:ebp = eresp, {
        rw HERESP, rw HCONDZERO2,
        unfold has_eq.eq, simp, 
        rw bvneq_r, simp, cases ebp; refl, apply HCONDZERO1
      },
      rw H,
      rw HERESP,
      apply poison_equiv_and, 
      { assumption },
      {
        constructor,
        apply b_equiv.ite,
        { apply b_equiv.eq, assumption, constructor },
        { cases HAEQ; cases HAEQ_a; assumption },
        { cases HBEQ_a, assumption },
      }
    },
    any_goals { assumption }
  },
  { -- operand 2 is not poison
    apply val_equiv.concrete_intty,
    {
      have H:ebp = eresp, {
        rw HERESP, rw HCONDZERO2,
        unfold has_eq.eq, simp,
        rw bvneq_r, simp, cases ebp; refl, apply HCONDZERO1
      },
      rw H,
      rw HERESP, rw HSRESP,
      apply poison_equiv_and,
      { assumption },
      { constructor,
        apply b_equiv.ite,
        { apply b_equiv.eq, assumption, constructor },
        { cases HAEQ; cases HAEQ_a; assumption },
        { cases HBEQ_a, assumption },
      }
    },
    {
      have H:HBEQ_ve = eres, {
        rw HERES,
        unfold has_eq.eq, simp,
        rw bvneq_r, simp, apply HCONDZERO1
      },
      rw H,
      rw HERES, rw HSRES,
      apply bv_equiv.ite,
      {
        apply b_equiv.eq, assumption, constructor
      }, {
        cases HAEQ,
        any_goals{ -- operand1 is either poison or concrete,
          -- but cond is ff, so operand1 is never used!
          intros H,
          unfold has_eq.eq at H, simp at H, rw bvneq_r at H, cases H, assumption
        }
      }, {
        intros, assumption
      }
    },
    assumption
  }
end

lemma selectop_equiv: ∀ (ss:irstate_smt) (se:irstate_exec) (szs sze:size)
    scond econd scondp econdp (sa:sbitvec szs) sap sb sbp (ea:bitvector sze) eap eb ebp
    sres sresp eres eresp
    (HSTEQ:irstate_equiv ss se)
    (HCONDEQ:val_equiv (irsem.valty.ival size.one scond scondp)
                       (irsem.valty.ival size.one econd econdp))
    (HAEQ:val_equiv (irsem.valty.ival szs sa sap)
                       (irsem.valty.ival sze ea eap))
    (HBEQ:val_equiv (irsem.valty.ival szs sb sbp)
                       (irsem.valty.ival sze eb ebp))
    (HSZEQ:szs = sze)
    (HSRES: (sres,sresp) = selectop irsem_smt scond scondp szs sa sap sb sbp)
    (HERES: (eres,eresp) = selectop irsem_exec econd econdp sze ea eap eb ebp),
  val_equiv (irsem.valty.ival szs sres sresp) (irsem.valty.ival sze eres eresp)
:= begin
  intros,
  unfold selectop at *,
  simp at *,
  injection HSRES,
  injection HERES,
  -- Condition is poison?
  cases HCONDEQ,
  { -- condition is poison.
    apply val_equiv.poison_intty,
    rw [h_2, h_4],
    rw HCONDEQ_a_2 at *,
    simp at *,
    rw poisonty_and_ff_op,
    apply poison_equiv_and_ff,
    assumption,
    assumption,
    { rw h_4, rw HCONDEQ_a_2, refl }
  },
  { -- condition is not poison.
    -- condition is either true or false,
    generalize HC: bitvector.eq econd (uint_like.from_z size.one 1) = c,
    cases c,
    { -- cond is ff.
      rw HCONDEQ_a_2 at *,
      rw h_3, rw h_4,
      unfold has_eq.eq,
      unfold has_comp.eq,
      rw HC, simp,
      apply selectop_equiv_false,
      { assumption },
      { -- condition is non-poison tt
        split,
        { have HC := bvneq_l HC,
          apply HC },
        { apply HCONDEQ_a_2 }
      },
      { -- exec and smt equiv select cond
        split, rw HCONDEQ_a_2, assumption,
        assumption
      },
      { apply HAEQ },
      { unfold has_and.and, rw poisonty_and_tt, apply HBEQ },
      { assumption },
      { apply HSRES },
      { rw poisonty_and_tt_op,
        unfold selectop }
    },
    { -- cond is tt
      rw HCONDEQ_a_2 at *, -- rw "no cond poison"
      rw h_4, -- rw eresp
      rw h_3, -- rw eres
      unfold has_eq.eq, unfold has_comp.eq,
      rw HC, simp,
      apply selectop_equiv_true,
      { assumption },
      { -- condition is non-poison tt
        split,
        { rw bveq at HC,
          apply HC },
        { apply HCONDEQ_a_2 }
      },
      { -- exec and smt equiv select cond
        split, rw HCONDEQ_a_2, assumption,
        assumption
      },
      { unfold has_and.and, simp, apply HAEQ },
      { apply HBEQ },
      { assumption },
      { apply HSRES },
      { rw poisonty_and_tt_op,
        unfold selectop }
    }
  }
end



/-
 - Theorems about icmp operation.
 -/

lemma icmpop_equiv: ∀ (szs sze:size) icond (sa:sbitvec szs) (sap:poisonty_smt)
    sb sbp (ea:bitvector sze) eap eb ebp
    sres sresp eres eresp
    (HAEQ:val_equiv (irsem.valty.ival szs sa sap) (irsem.valty.ival sze ea eap))
    (HBEQ:val_equiv (irsem.valty.ival szs sb sbp) (irsem.valty.ival sze eb ebp))
    (HSZEQ:szs = sze)
    (HSRES: (sres,sresp) = icmpop irsem_smt szs icond sa sap sb sbp)
    (HERES: (eres,eresp) = icmpop irsem_exec sze icond ea eap eb ebp),
  val_equiv (irsem.valty.ival size.one sres sresp)
               (irsem.valty.ival size.one eres eresp)
:= begin
  intros,
  cases icond,
  all_goals {
    unfold icmpop at *,
    delta icmpop._match_1 at *,
    simp at *,
    delta id_rhs at *,
    injection HSRES,
    injection HERES,
    unfold coe at *, unfold lift_t at *, unfold has_lift_t.lift at *,
    unfold coe_t at *,unfold has_coe_t.coe at *,unfold coe_b at *,
    unfold has_coe.coe at * },
  any_goals {
    rw [h_1, h_2, h_3, h_4],
    cases eresp,
    { -- If the reuslt is poison
      apply val_equiv.poison_intty,
      apply poison_equiv_and,
      any_goals {
        apply val_equiv_eqpoison,
        assumption
      },
      refl,
      rw ← h_4, simp
    },
    { -- If the result isn't poison
      -- Operands should not be poison! Let's solve this.
      cases HAEQ,
      { -- operand 1 is poison -> exfalso.
        rw HAEQ_a_2 at *,
        injection HERES,
        injection h_6
      },
      cases HBEQ,
      { -- operand 2 is poison -> exfalso.
        rw HBEQ_a_2 at *,
        injection HERES,
        cases eap,
        injection h_6,
        injection h_6
      },
      -- Now apply vppair_equiv.concrete to the goal.
      apply val_equiv.concrete_intty,
      apply poison_equiv_and,
      any_goals { assumption, done },
      apply bv_equiv.of_bool,
      constructor,
      any_goals { assumption, done },
      rw HAEQ_a_2, rw HBEQ_a_2, refl
    }
  }
end

/-
 - Theorems about cast operation.
 -/

lemma castop_equiv: ∀ (efromsz sfromsz etosz stosz:size) (code:uopcode)
    (sx:sbitvec sfromsz) sxp (ex:bitvector efromsz) exp sres sresp eres eresp
    (HXEQ:val_equiv (irsem.valty.ival sfromsz sx sxp) (irsem.valty.ival efromsz ex exp))
    (HFROMSZEQ:sfromsz = efromsz) (HTOSZEQ:stosz = etosz)
    (HSRES: (sres,sresp) = castop irsem_smt sfromsz code sx sxp stosz)
    (HERES: (eres,eresp) = castop irsem_exec efromsz code ex exp etosz),
  val_equiv (irsem.valty.ival stosz sres sresp) (irsem.valty.ival etosz eres eresp)
:= begin
  intros,
  have Hsz:decidable (efromsz.val < etosz.val), apply_instance,
  cases Hsz,
  {
    have Hsz':¬sfromsz.val < stosz.val,
    { rw HFROMSZEQ, rw HTOSZEQ, assumption },
    unfold castop at *,
    simp [Hsz'] at HSRES,
    simp [Hsz] at HERES,
    
    have Hsz2:decidable (efromsz.val = etosz.val), apply_instance,
    cases Hsz2,
    {
      have Hsz2':¬sfromsz.val = stosz.val,
      { rw HFROMSZEQ, rw HTOSZEQ, assumption },
      rw if_neg at HSRES; try { assumption },
      rw if_neg at HERES; try { assumption },
      injection HSRES,
      injection HERES,
      rw [h_1, h_2, h_3, h_4],
      cases code,
      any_goals {
        cases HXEQ,
        { -- If input is poison, output is also poison!
          apply val_equiv.poison_intty,
          assumption, assumption,
          simp, assumption
        },
        { -- If input is non-poison..
          rw HFROMSZEQ at *,
          rw HTOSZEQ at *,
          apply val_equiv.concrete_intty,
          { cases HXEQ_a,
            constructor, assumption },
          { apply bv_equiv.trunc, apply nat.not_gt_not_eq_implies_lt,
            { assumption }, { apply neq_symm, assumption },
            assumption },
          { assumption }
        }
      }
    },
    {
      rw if_pos at HERES; try { assumption },
      rw if_pos at HSRES; try { assumption },
      injection HERES,
      injection HSRES,
      rw [h_1, h_2, h_3, h_4],
      cases HXEQ,
      { -- If input is poison
        apply val_equiv.poison_intty,
        assumption, assumption, assumption
      },
      { -- If input is non-poison..
        rw HFROMSZEQ at *,
        rw HTOSZEQ at *,
        apply val_equiv.concrete_intty,
        { assumption },
        { constructor },
        { assumption }
      },
      { rw [HFROMSZEQ, HTOSZEQ], assumption }
    }
  },
  { -- tosz > fromsz
    have Hsz':sfromsz.val < stosz.val,
    { rw HFROMSZEQ, rw HTOSZEQ, assumption },
    unfold castop at *,
    simp [Hsz'] at HSRES,
    simp [Hsz] at HERES,
    injection HSRES,
    injection HERES,
    rw [h_1, h_2, h_3, h_4],

    cases HXEQ,
    { -- input is poison
      apply val_equiv.poison_intty, assumption, assumption, simp, assumption
    }, { -- input is not poison
      cases HXEQ_a,
      rw HTOSZEQ,
      cases code; unfold castop._match_1; apply val_equiv.concrete_intty,
      any_goals { assumption, done },
      any_goals { constructor, assumption, done },
      any_goals {
        apply bv_equiv.sext, assumption, assumption
      },
      any_goals {
        apply bv_equiv.zext, assumption, assumption
      },
    }
  }
end


/-
 - Theorems about bop operations.
 -/

lemma bop_ub_equiv: ∀ (szs sze:size) (code:bopcode)
    (sa:sbitvec szs) sap (sb:sbitvec szs) sbp
    (sub:sbool) (eub:bool)
    (ea:bitvector sze) eap (eb:bitvector sze) ebp
    (HSZEQ:szs = sze)
    (HAEQ:val_equiv (valty.ival szs sa sap) (valty.ival sze ea eap))
    (HBEQ:val_equiv (valty.ival szs sb sbp) (valty.ival sze eb ebp))
    (HSRES: sub = bop_ub irsem_smt szs code sa sap sb sbp)
    (HERES: eub = bop_ub irsem_exec sze code ea eap eb ebp),
  b_equiv sub eub
:= begin
  intros,
  cases code; unfold bop_ub at *; unfold bop_isdiv at *; simp at *,
  any_goals { -- when it is not division
    rw [HSRES, HERES], constructor, done
  },
  any_goals { -- bopcode is unsigned division.
    have HBPEQ: poison_equiv sbp ebp,
    { apply val_equiv_eqpoison, apply HBEQ },
    cases HBEQ,
    { -- if operand2 are poison
      rw [HSRES, HERES],
      rw HBEQ_a_2 at *, -- ebp to ff
      apply b_equiv_and_ff,
      { cases HBPEQ, unfold has_and.and, unfold_coes,
        apply b_equiv_and_ff, apply HBPEQ_a }
    },
    { -- if operand2 are not poison
      rw [HSRES, HERES],
      apply b_equiv_and,
      { rw ← poison_bool_equiv, constructor, apply b_equiv_and,
        { cases HBEQ_a, apply HBEQ_a_a },
        { cases HBEQ_a_2, cases HBEQ_a_2,
          unfold_coes, unfold eq2p, unfold b2p,
          unfold has_ne.ne, unfold has_comp.ne,
          apply b_equiv.ite, apply b_equiv.ne, assumption, constructor,
          constructor, constructor } },
      { constructor },
    }
  },
  any_goals { -- bopcode is signed division.
    have HBPEQ: poison_equiv sbp ebp,
    { apply val_equiv_eqpoison, apply HBEQ },
    cases HBEQ,
    { -- if operand2 are poison
      rw [HSRES, HERES],
      rw HBEQ_a_2 at *, -- ebp to ff
      apply b_equiv_and_ff,
      { cases HBPEQ, apply b_equiv_and_ff, apply HBPEQ_a }
    },
    { -- if operand2 are not poison, SIGNED DIVISION
      rw [HSRES, HERES],
      apply b_equiv_and,
      { rw ← poison_bool_equiv, constructor, apply b_equiv_and,
        { cases HBEQ_a, assumption },
        { apply b_equiv.ite,
          {
            cases HBEQ_a,
            apply b_equiv.ne, assumption, constructor
          },
          constructor, constructor
        }
      },
      { unfold eq2p, unfold b2p,
        cases HBEQ_a,
        unfold_coes,
        apply b_equiv_or,
        { -- consraint on dividend
          cases HAEQ,
          { cases HAEQ_a, rw HAEQ_a_2, simp, rw poisonty_and_ff_op,
            apply b_equiv_and_ff, rw HAEQ_a_2 at HAEQ_a_a,
            apply HAEQ_a_a
          },
          { apply b_equiv_and,
            { cases HAEQ_a, assumption },
            { cases HAEQ_a_2,
              apply b_equiv.ite,
              apply b_equiv.ne,
              assumption,
              apply bv_equiv.const,
              constructor, constructor
            }
          }
        },
        { -- constraint on divisor
          apply b_equiv.ite,
          { apply b_equiv.ne, assumption, constructor },
          { constructor },
          { constructor }
        }
      }
    },
    done
  }
end

-- bop_poison preserves equivalence
lemma bop_poison_equiv : ∀ (sz:size) bopc (sa:sbitvec sz) sb ea eb sp ep
    (HAEQ:bv_equiv sa ea) (HBEQ:bv_equiv sb eb)
    (HSEQ:sp = bop_poison irsem_smt sz bopc sa sb)
    (HEEQ:ep = bop_poison irsem_exec sz bopc ea eb),
  poison_equiv sp ep
:= begin
  intros,
  unfold bop_poison at *,
  cases bopc,
  any_goals {
    simp at *,
    unfold b2p at *,
    rw [HSEQ, HEEQ],
    constructor, apply b_equiv_ite, constructor,
    done
  },
  any_goals { -- for all remaining goals..
    simp at *,
    unfold bop_poison._match_1 at *,
    unfold b2p at *,
    rw [HSEQ, HEEQ],
    constructor,
    apply b_equiv_ite; try {constructor, done},
    try { apply b_equiv.ult, assumption, apply bv_equiv.const }
  }
end

-- If bop(op1, op2) never raises UB,
-- it never raises UB even if operands are not poison (trivially)
lemma bop_ub_refines: ∀ sz bopc (ea:bitvector sz) eap eb ebp
  (HNOUB:irsem_exec.bbl.tt =
          bop_ub irsem_exec sz bopc ea eap eb ebp),
  irsem_exec.bbl.tt = bop_ub irsem_exec sz bopc ea tt eb tt
:= begin
  intros,
  cases bopc; try { unfold bop_ub at *, simp, done },
  any_goals { -- unsigned divisions!
    unfold bop_ub at *,
    unfold bop_isdiv at *,
    simp at *,
    unfold_coes at *,
    unfold id at *,
  
    cases ebp, -- divisor is poison?
    { -- divisor cannot be poison, according to HNOUB
      rw poisonty_and_ff_op at HNOUB,
      rw poisonty_and_ff_op at HNOUB,
      cases HNOUB
    },
    { assumption }
  },
  any_goals { -- signed divisions!
    unfold bop_ub at *,
    unfold bop_isdiv at *,
    simp at *,
    unfold_coes at *,
    unfold id at *,
  
    cases ebp, -- divisor is poison?
    { -- divisor cannot be poison, according to HNOUB
      rw poisonty_and_ff_op at HNOUB,
      rw poisonty_and_ff_op at HNOUB,
      cases HNOUB
    },
    { cases eap, -- op1 is poison?
      { rw poisonty_and_ff_op at HNOUB,
        repeat { rw poisonty_and_tt_op at * },
        rw poisonty_or_ff_op at *,
        have HNOUB := boolty_and_inj (eq.symm HNOUB),
        cases HNOUB with H1 H2,
        rw H1, rw H2,
        rw boolty_or_tt2_op,
        refl
      },
      {
        assumption
      }
    }
  }
end

lemma bop_val_equiv: ∀  (sz:size) (code:bopcode)
    (sa:sbitvec sz) (sb:sbitvec sz) ea eb sres eres
    (HAEQ:bv_equiv sa ea) (HAEQ:bv_equiv sb eb)
    (HSRES: sres = bop_val irsem_smt sz code sa sb)
    (HERES: eres = bop_val irsem_exec sz code ea eb)
    (HNOTUB: bop_ub irsem_exec sz code ea
              (irsem_exec.pbl.tt) eb (irsem_exec.pbl.tt) = (irsem_exec.bbl.tt))
    (HNOTPOISON: bop_poison irsem_exec sz code ea eb = (irsem_exec.bbl.tt)),
  bv_equiv sres eres
:= begin
  intros,
  rw [HSRES, HERES],
  cases code; unfold bop_val,
  any_goals { -- add, sub, mul, and, or, xor
    constructor; assumption, done },
  any_goals { -- udiv, urem
    unfold bop_ub at HNOTUB,
    simp [if_pos] at HNOTUB,
    delta eq2p at HNOTUB, simp at HNOTUB,
    unfold uint_like.zero at HNOTUB,
    unfold_lops_at_all, unfold_coes at HNOTUB,
    simp at HNOTUB,
    constructor; assumption,
    done
  },
  any_goals { -- sdiv, srem
    unfold bop_ub at HNOTUB,
    simp [if_pos] at HNOTUB,
    delta eq2p at HNOTUB, simp at HNOTUB,
    try { unfold has_mod.mod, unfold uint_like.srem },
    try { unfold has_div.div, unfold uint_like.sdiv },
    unfold_lops_at_all,
    unfold_coes at *,
    unfold id at *,
    unfold uint_like.zero at HNOTUB,
    have HNOTUB := poisonty_and_inj HNOTUB,
    cases HNOTUB, -- x / 0 should not happen
    have HNOTUB2 := poisonty_or_inj HNOTUB_right,
    try { apply bv_equiv.sdiv },
    try { apply bv_equiv.srem },
    assumption, assumption, rw boolty_and_tt at HNOTUB_left, assumption,
    rw boolty_and_tt at HNOTUB2, apply HNOTUB2
  },
  any_goals { -- shl, lshr, ashr
    unfold bop_poison at HNOTPOISON,
    simp at HNOTPOISON,
    unfold bop_poison._match_1 at HNOTPOISON,
    try { apply bv_equiv.shl };
    try { apply bv_equiv.lshr };
    try { apply bv_equiv.ashr };
    try { assumption }
  }
end

-- the results returned by two bop_poison_flag are equivalent.
lemma bop_poison_flag_equiv: ∀ sz (flag:bopflag) bopc
    (sa:sbitvec sz) sb (ea:bitvector sz) eb sp ep
    (HNOUB:irsem_exec.bbl.tt = bop_ub irsem_exec sz bopc ea tt eb tt)
    (HAEQ:bv_equiv sa ea) (HBEQ:bv_equiv sb eb)
    (HSEQ:sp = bop_poison_flag irsem_smt sz bopc flag sa sb)
    (HEEQ:ep = bop_poison_flag irsem_exec sz bopc flag ea eb),
  poison_equiv sp ep
:= begin
  intros,
  cases flag; unfold bop_poison_flag at *,
  any_goals { -- "nsw", "nuw"
    rw [HSEQ, HEEQ], constructor, apply b_equiv.not,
    -- show bop_overflow_check equivalence.
    cases bopc; unfold bop_overflow_check at *; simp at *,
    any_goals { -- add 
      -- 'any_goals' helps lemma proving less dependent to the order of definition
      -- of constructors of bopcode.
      unfold has_overflow_check.add_chk
             has_overflow_check.sub_chk
             has_overflow_check.mul_chk
             has_overflow_check.shl_chk at *,
      unfold b2p,
      apply b_equiv_ite,
      try { apply add_overflow_chk; assumption },
      try { apply sub_overflow_chk; assumption },
      try { apply mul_overflow_chk; assumption },
      try { apply shl_overflow_chk; assumption },
      done
    }
  },
  { -- exact
    rw [HSEQ, HEEQ], clear HEEQ, clear HSEQ,
    constructor, apply b_equiv.not,
    cases bopc; unfold bop_exact_check at *; simp at *;
        unfold bop_exact_check._match_1; unfold eq2p; simp;
        unfold b2p; apply b_equiv_ite,
    any_goals
    { -- All other instructions which cannot have 'exact'.
      apply b_equiv.ne; assumption, done },
    any_goals { -- udiv, urem
      apply b_equiv.ne, apply bv_equiv.urem; try { assumption },
      -- We should derive divisor != 0 from HNOUB.
      { unfold bop_ub at HNOUB, simp at HNOUB, unfold eq2p at HNOUB,
      unfold_lops_at_all, unfold_coes at HNOUB, unfold id at HNOUB,
      simp at HNOUB, unfold uint_like.zero at HNOUB, rw ← HNOUB, congr },
      constructor
    },
    any_goals { -- sdiv, srem
      -- We should derive divisor != 0 from HNOUB.
      unfold bop_ub at HNOUB, simp at HNOUB, unfold eq2p at HNOUB,
      simp at HNOUB,
      have HNOUB := boolty_and_inj (eq.symm HNOUB),
      cases HNOUB with NOZERO NOINTMIN, -- !(n/0) ∧ !(INT_MIN/-1)|
      unfold_lops_at_all, unfold_coes at *, unfold id at *,

      apply b_equiv.ne, apply bv_equiv.srem; try { assumption },
      rw boolty_and_tt at NOZERO, apply NOZERO,
      rw boolty_and_tt at NOINTMIN,
      have NOINTMIN := boolty_or_inj NOINTMIN,
      apply NOINTMIN,
      constructor
    },
    any_goals {
      -- lshr, ashr
      -- These cases are a bit messy.
      apply b_equiv.ne, any_goals { assumption },
      apply bv_equiv.shl,
      {
        try { apply bv_equiv.lshr },
        try { apply bv_equiv.ashr },
        assumption,
        apply bvequiv_urem, assumption,
        apply bvult_mod_sz
      },
      apply bvequiv_urem, assumption,
      apply bvult_mod_sz
    }
  }
end

-- Given a list of bopflag, the results of bop_poison_all are equivalent..
lemma bop_poison_all_equiv: ∀ sz (flags:list bopflag) bopc
    (sa:sbitvec sz) sb (ea:bitvector sz) eb sp ep
    (HNOUB:irsem_exec.bbl.tt = bop_ub irsem_exec sz bopc ea tt eb tt)
    (HAEQ:bv_equiv sa ea) (HBEQ:bv_equiv sb eb)
    (HSEQ:sp = bop_poison_all irsem_smt sz bopc flags sa sb)
    (HEEQ:ep = bop_poison_all irsem_exec sz bopc flags ea eb),
  poison_equiv sp ep
:= begin
  intros,
  revert sp ep,
  induction flags,
  {
    intros,
    unfold bop_poison_all at HSEQ HEEQ,
    simp at HSEQ HEEQ,
    rw [HSEQ, HEEQ],
    apply bop_poison_equiv, apply HAEQ, apply HBEQ,
    simp, simp
  },
  {
    intros,
    unfold bop_poison_all at HSEQ HEEQ flags_ih,
    simp at HSEQ HEEQ,
    rw [HEEQ, HSEQ],
    {
      -- if "one flag" is appended.
      apply poison_equiv_and,
      {
        apply flags_ih, simp
      },
      {
        apply bop_poison_flag_equiv, apply HNOUB, apply HAEQ, apply HBEQ,
        simp, simp
      }
    }
  }
end

-- If bop yields non-poison value, inputs are also non-poison
lemma bop_exec_nonpoison_implies: ∀ (sz:size) bopc flags ea eap eb ebp
    (eub:irsem_exec.boolty) eres (eresp:irsem_exec.poisonty)
    (HEEQ:(eub, (eres, eresp)) = bop irsem_exec sz bopc flags ea eap eb ebp)
    (HNOUB: eub = tt)
    (HENOPOISON:eresp = irsem_exec.pbl.tt),
    eap = tt ∧ ebp = tt
:= begin
  intros,
  cases eap; cases ebp,
  { -- (poison, poison)
    cases bopc,
    any_goals {
      unfold bop at HEEQ,
      simp at HEEQ,
      injection HEEQ with HEEQUB HEEQ,
      injection HEEQ with HEEQ HEEQP,
      rw poisonty_and_ff_op at HEEQP,
      rw poisonty_and_ff2_op at HEEQP,
      rw HEEQP at HENOPOISON, cases HENOPOISON
    }
  },
  any_goals { -- (poison, non-poison)
    cases bopc,
    any_goals {
      unfold bop at HEEQ,
      simp at HEEQ,
      injection HEEQ with HEEQUB HEEQ,
      injection HEEQ with HEEQ HEEQP,
      try { rw poisonty_and_ff_op at HEEQP },
      try { rw poisonty_and_ff2_op at HEEQP },
      try { rw poisonty_and_ff2_op at HEEQP },
      rw HEEQP at HENOPOISON, cases HENOPOISON
    }
  },
  simp
end

lemma bop_equiv: ∀ (szs sze:size) bopc flags (sa:sbitvec szs) sap sb sbp
    (ea:bitvector sze) eap eb ebp
    (HAEQ:val_equiv (valty.ival szs sa sap) (valty.ival sze ea eap))
    (HBEQ:val_equiv (valty.ival szs sb sbp) (valty.ival sze eb ebp))
    (HSZEQ:szs = sze)
    (sub:irsem_smt.boolty) sres (sresp:irsem_smt.poisonty)
    (eub:irsem_exec.boolty) eres (eresp:irsem_exec.poisonty)
    (HSEQ:(sub, (sres, sresp)) = bop irsem_smt szs bopc flags sa sap sb sbp)
    (HEEQ:(eub, (eres, eresp)) = bop irsem_exec sze bopc flags ea eap eb ebp),
  b_equiv sub eub ∧ -- both have same UB
  (eub = irsem_exec.bbl.tt →
    val_equiv (valty.ival szs sres sresp) (valty.ival sze eres eresp))
    -- If there's no UB, both have same (value, poison).
    -- This assumption is needed due to the existence of 'exact'.
:= begin
  intros,
  unfold bop at *,
  simp at HSEQ HEEQ,
  injection HSEQ with HSEQUB HSEQVP,
  injection HSEQVP with HSEQV HSEQP,
  injection HEEQ with HEEQUB HEEQVP,
  injection HEEQVP with HEEQV HEEQP,

  split,
  {-- ub equivance
    apply bop_ub_equiv,
    { apply HSZEQ },
    { apply HAEQ },
    { apply HBEQ },
    { apply HSEQUB },
    { apply HEEQUB }
  },
  { -- value × poison equivalence
    intros HNOUB,
    rw HEEQUB at HNOUB,
    rw [HEEQP, HSEQP],
    cases eresp,
    { -- if the result is poison, concrete value doesn't matter.
      apply val_equiv.poison_intty,
      {
        cases HAEQ, 
        { -- If input operand1s are poison..
          rw HAEQ_a_2 at *, simp,
          rw poisonty_and_ff_op, rw poisonty_and_ff2_op,
          apply poison_equiv.intro,
          apply b_equiv_and_ff2,
          apply b_equiv_and_ff,
          cases HAEQ_a, assumption
        },
        { -- okay, input operand1 are concrete.
          cases HBEQ,
          { -- If input operand2s are poison..
            rw HBEQ_a_2 at *, simp,
            rw poisonty_and_ff2_op, rw poisonty_and_ff2_op,
            apply poison_equiv.intro,
            apply b_equiv_and_ff2,
            apply b_equiv_and_ff2,
            cases HBEQ_a, assumption
          },
          { -- okay, both operands are concrete!!
            apply poison_equiv_and,
            {
              cases HAEQ_a, cases HBEQ_a,
              apply bop_poison_all_equiv,
              { apply bop_ub_refines, apply (eq.symm HNOUB) },
              assumption, assumption, simp, simp
            },
            { apply poison_equiv_and; assumption }
          }
        }
      },
      { assumption },
      { rw ← HEEQP, refl }
    },
    { -- If there's no UB and poison, the result values are equiv.
      have HNOPOISON: eap = tt ∧ ebp = tt, {
        apply bop_exec_nonpoison_implies,
        apply HEEQ,
        { rw HNOUB at HEEQUB, assumption },
        refl
      },
      cases HNOPOISON with HNOPOISON_A HNOPOISON_B,
      -- let's make bv_equiv!
      cases HAEQ; cases HBEQ; try {
      rw HNOPOISON_A at *,
      rw HNOPOISON_B at *,
      try { cases HAEQ_a_2 },
      try { cases HBEQ_a_2 },
      },
      -- HAEQ_a_1_a, HBEQ_a_1_a are bv_equivs.
      apply val_equiv.concrete_intty,
      {
        apply poison_equiv_and,
        apply bop_poison_all_equiv,
        { rw ← bop_ub_refines, rw HNOUB },
        { assumption },
        { assumption },
        { simp },
        { simp },
        { apply poison_equiv_and, assumption, assumption
        }
      },
      {
        apply bop_val_equiv,
        apply HAEQ_a_1, apply HBEQ_a_1, apply HSEQV, assumption,
        rw poisonty_tt, rw ← bop_ub_refines, simp,
        rw HNOUB,

        have HEEQP := boolty_and_inj (eq.symm HEEQP),
        cases HEEQP,
        have ANSW := bop_poison_peel HEEQP_left,
        rw ANSW, simp,
        refl
      },
      { rw ← HEEQP, simp }
    }
  }
end


/-
 - Theorems about step_exe.
 -/

lemma bop_step_both: ∀ (ss:irstate_smt) (se:irstate_exec) (lhsname:string)
    (oss':option irstate_smt) (ose':option irstate_exec)
    (sa sb:valty_smt) (ea eb:valty_exec)
    (bopc:bopcode) (flags:list bopflag)
    (HSTEQ: irstate_equiv ss se)
    (HVAEQ: has_no_ub se = tt → val_equiv sa ea)
    (HVBEQ: has_no_ub se = tt → val_equiv sb eb)
    (HASZEQ: equals_size sa ea = tt)
    (HBSZEQ: equals_size sb eb = tt)
    (HOSS': oss' = step_bop irsem_smt sa sb bopc flags ss lhsname)
    (HOSE': ose' = step_bop irsem_exec ea eb bopc flags se lhsname),
  none_or_some oss' ose' (λ ss' se', irstate_equiv ss' se')
:= begin
  intros,
  cases HSTEQ,
  { -- previous state is not UB!
    unfold has_no_ub at HVAEQ HVBEQ,
    have HVAEQ := HVAEQ HSTEQ_a_2,
    have HVBEQ := HVBEQ HSTEQ_a_2, -- prepare vppair_equivs!
    cases sa with sa_sz sa_a sap, -- unfold operands
    cases sb with sb_sz sb_a sbp,
    cases ea with ea_sz ea_a eap,
    cases eb with eb_sz eb_a ebp,
    unfold equals_size at HASZEQ HBSZEQ,
    have HASZEQ := to_bool_prop (sa_sz = ea_sz) HASZEQ,
    have HBSZEQ := to_bool_prop (sb_sz = eb_sz) HBSZEQ,
    unfold step_bop at *,
    have HSZDEC:decidable (sa_sz = sb_sz), apply_instance,
    cases HSZDEC,
    { -- Sizes are different -> should return none
      have HSZDEC':¬(ea_sz = eb_sz),
      { rw ← HASZEQ, rw ← HBSZEQ, assumption },
      simp [HSZDEC] at HOSS',
      simp [HSZDEC'] at HOSE',
      left, split; assumption
    },
    { -- Sizes are the same!
      have HSZDEC':(ea_sz = eb_sz),
      { rw ← HASZEQ, rw ← HBSZEQ, assumption },
      simp [HSZDEC] at HOSS',
      simp [HSZDEC'] at HOSE',
      generalize HSRES: bop irsem_smt sa_sz bopc
                        flags sa_a sap (cast (by rw HSZDEC) sb_a) sbp = sres,
      generalize HERES: bop irsem_exec ea_sz bopc
                        flags ea_a eap (cast (by rw HSZDEC') eb_a) ebp = eres,
      rw HSRES at HOSS',
      rw HERES at HOSE',
      cases eres with eub eresvp,
      cases eresvp with eresv eresp,
      cases sres with sub sresvp,
      cases sresvp with sresv sresp,
      unfold step_bop._match_2 at HOSS' HOSE',
      cases oss' with ss'; try { injection HOSS' },
      cases ose' with se'; try { injection HOSE' },

      right,
      apply exists.intro ss',
      apply exists.intro se',
      split, refl,
      split, refl,
      -- show irstate_equiv of the targets!
      -- now it's time to use bop_equiv.
      have HRESEQ:(b_equiv sub eub ∧ -- both have same UB
        (eub = bool_like.tt irsem_exec.boolty →
        val_equiv  (valty.ival sa_sz sresv sresp)
                   (valty.ival ea_sz eresv eresp))), {
        apply bop_equiv,
        { apply HVAEQ },
        { apply val_equiv_rwsize2',
            apply (eq.symm HSZDEC),
            apply (eq.symm HSZDEC'),
            apply HVBEQ },
        { apply HASZEQ },
        { rw HSRES },
        { rw HERES }
      },
      rw h_1,
      rw h_2,
      apply irstate.updatereg_equiv,
      { cases HRESEQ, intros HNOUB, apply HRESEQ_right,
        unfold irstate.updateub at HNOUB,
        simp at HNOUB, unfold has_no_ub at HNOUB,
        have HNOUB := boolty_and_inj HNOUB,
        cases HNOUB, assumption },
      { assumption },
      { apply irstate.updateub_equiv,
        cases HRESEQ, assumption,
        cases HRESEQ, assumption }
    }
  },
  { -- previous state was UB
    cases sa with sa_sz sa_a sap, -- unfold operands
    cases sb with sb_sz sb_a sbp,
    cases ea with ea_sz ea_a eap,
    cases eb with eb_sz eb_a ebp,
    unfold step_bop at *,
    simp at HASZEQ,
    simp at HBSZEQ,
    have HSZDEC:decidable (sa_sz = sb_sz), apply_instance,
    cases HSZDEC,
    { -- Sizes are different -> should return none
      have HSZDEC': ¬ ea_sz = eb_sz, {
        rw ← HASZEQ, rw ← HBSZEQ, assumption
      },
      simp [HSZDEC] at HOSS',
      simp [HSZDEC'] at HOSE',
      left, split; assumption
    },
    { -- Sizes are equivalent
      have HSZDEC': ea_sz = eb_sz, {
        rw ← HASZEQ, rw ← HBSZEQ, assumption
      },
      simp [HSZDEC] at HOSS',
      simp [HSZDEC'] at HOSE',
      generalize HSRES: bop irsem_smt sa_sz bopc
                          flags sa_a sap (cast (by rw HSZDEC) sb_a) sbp = sres,
      generalize HERES: bop irsem_exec ea_sz bopc
                          flags ea_a eap (cast (by rw HSZDEC') eb_a) ebp = eres,
      rw HSRES at HOSS',
      rw HERES at HOSE',
      cases eres with eub eresvp,
      cases eresvp with eresv eresp,
      cases sres with sub sresvp,
      cases sresvp with sresv sresp,
      unfold step_bop._match_2 at HOSS' HOSE',
      cases oss' with ss'; try { injection HOSS' },
      cases ose' with se'; try { injection HOSE' },

      right,
      apply exists.intro ss',
      apply exists.intro se',
      split, refl,
      split, refl,
      -- split ∧ in ss', se'
      cases ss',
      cases se',
      -- unfold irstate.updatereg/updateub to reveal UB variables
      unfold irstate.updatereg at h_1 h_2,
      unfold irstate.updateub at h_1 h_2,
      injection h_2, injection h_1,
      simp at h_3, simp at h_5,
      -- show irstate_equiv of the targets!
      -- now it's time to use bop_equiv.
      apply irstate_equiv.ub,
      { -- Show b_equiv ss'_fst se'_fst
        rw h_3, rw h_5,
        rw HSTEQ_a_1,
        apply b_equiv_and_ff,
        { rw HSTEQ_a_1 at HSTEQ_a, assumption }
      },
      {
        rw HSTEQ_a_1 at h_3, apply h_3
      },
      {
        simp at h_4 h_6,
        rw [h_4, h_6],
        apply regfile.sametypes_update,
        assumption,
        unfold to_ival,
        unfold equals_size, simp, assumption
      }
    }
  }
end

lemma icmpop_step_both: ∀ (ss:irstate_smt) (se:irstate_exec) (lhsname:string)
    (oss':option irstate_smt) (ose':option irstate_exec)
    (sa sb:valty_smt) (ea eb:valty_exec)
    (icond:icmpcond)
    (HSTEQ: irstate_equiv ss se)
    (HVAEQ: has_no_ub se = tt → val_equiv sa ea)
    (HVBEQ: has_no_ub se = tt → val_equiv sb eb)
    (HASZEQ: equals_size sa ea = tt)
    (HBSZEQ: equals_size sb eb = tt)
    (HOSS': oss' = step_icmpop irsem_smt sa sb icond ss lhsname)
    (HOSE': ose' = step_icmpop irsem_exec ea eb icond se lhsname),
  none_or_some oss' ose' (λ ss' se', irstate_equiv ss' se')
:= begin
  intros,
  cases sa with sa_sz sa sap,
  cases sb with sb_sz sb sbp,
  cases ea with ea_sz ea eap,
  cases eb with eb_sz eb ebp,
  unfold step_icmpop at *,
  -- prepare for some good properties about size equality
  simp at HASZEQ,
  simp at HBSZEQ,
  have HSZDEC:decidable (sa_sz = sb_sz), apply_instance,
  cases HSZDEC,
  { -- sa_sz neq sb_sz
    have HSZNEQ:(¬ ea_sz = eb_sz), {
      rw HASZEQ at HSZDEC,
      rw HBSZEQ at HSZDEC,
      assumption
    },
    simp [HSZDEC] at HOSS',
    simp [HSZNEQ] at HOSE',
    left, split; assumption
  },
  {
    have HSZEQ:(ea_sz = eb_sz), {
      rw HASZEQ at HSZDEC,
      rw HBSZEQ at HSZDEC,
      assumption
    },
    simp [HSZDEC] at HOSS',
    simp [HSZEQ] at HOSE',

    generalize HSRES:icmpop irsem_smt sa_sz icond sa sap (cast (by rw HSZDEC) sb) sbp = sres,
    generalize HERES:icmpop irsem_exec ea_sz icond ea eap (cast (by rw HSZEQ) eb) ebp = eres,
    rw HSRES at HOSS',
    rw HERES at HOSE',
    cases eres with eresv eresp,
    cases sres with sresv sresp,
    right,
    apply exists.intro (irstate.updatereg irsem_smt ss lhsname (valty.ival size.one sresv sresp)),
    apply exists.intro (irstate.updatereg irsem_exec se lhsname (valty.ival size.one eresv eresp)),
    split, assumption,
    split, assumption,
    apply irstate.updatereg_equiv,
    { intros HNOUB,
      have HVAEQ := HVAEQ HNOUB,
      have HVBEQ := HVBEQ HNOUB,
      apply icmpop_equiv, -- HERE!
      { apply HVAEQ },
      { apply val_equiv_rwsize2',
        rw HSZDEC, rw HSZEQ, assumption },
      { assumption },
      { rw HSRES },
      { rw HERES }
    },
    simp,
    assumption
  }
end

lemma selectop_step_both: ∀ (ss:irstate_smt) (se:irstate_exec) (lhsname:string)
    (oss':option irstate_smt) (ose':option irstate_exec)
    (sa sb sc:valty_smt)
    (ea eb ec:valty_exec)
    (HSTEQ: irstate_equiv ss se)
    (HVAEQ: has_no_ub se = tt → val_equiv sa ea)
    (HVBEQ: has_no_ub se = tt → val_equiv sb eb)
    (HVCEQ: has_no_ub se = tt → val_equiv sc ec)
    (HASZEQ: equals_size sa ea = tt)
    (HBSZEQ: equals_size sb eb = tt)
    (HCSZEQ: equals_size sc ec = tt)
    (HOSS': oss' = step_selectop irsem_smt sc sa sb ss lhsname)
    (HOSE': ose' = step_selectop irsem_exec ec ea eb se lhsname),
  none_or_some oss' ose' (λ ss' se', irstate_equiv ss' se')
:= begin
  intros,
  cases sa with sa_sz sa sap,
  cases sb with sb_sz sb sbp,
  cases sc with sc_sz sc scp,
  cases ea with ea_sz ea eap,
  cases eb with eb_sz eb ebp,
  cases ec with ec_sz ec ecp,
  simp at HASZEQ,
  simp at HBSZEQ,
  simp at HCSZEQ,
  unfold step_selectop at HOSS' HOSE',
  have HCSZONE:decidable (sc_sz = size.one), apply_instance,
  cases HCSZONE,
  { -- condition bitsize is not 1 -> stuck
    have HCSZONE':(¬ ec_sz = size.one), {
      rw HCSZEQ at HCSZONE,
      assumption
    },
    simp [HCSZONE] at HOSS',
    simp [HCSZONE'] at HOSE',
    left, split; assumption
  },{
    have HCSZONE':(ec_sz = size.one), {
      rw HCSZEQ at HCSZONE,
      assumption
    },
    simp [HCSZONE] at HOSS',
    simp [HCSZONE'] at HOSE',

    have HSZDEC:decidable (sa_sz = sb_sz), apply_instance,
    cases HSZDEC,
    { -- sa_sz neq sb_sz
      have HSZNEQ:(¬ ea_sz = eb_sz), {
        rw HASZEQ at HSZDEC,
        rw HBSZEQ at HSZDEC,
        assumption
      },
      simp [HSZDEC] at HOSS',
      simp [HSZNEQ] at HOSE',
      left, split; assumption
    },
    {
      have HSZEQ:(ea_sz = eb_sz), {
        rw HASZEQ at HSZDEC,
        rw HBSZEQ at HSZDEC,
        assumption
      },
      simp [HSZDEC] at HOSS',
      simp [HSZEQ] at HOSE',

      generalize HSRES:selectop irsem_smt (cast (by rw HCSZONE) sc) scp
                      sa_sz sa sap (cast (by rw HSZDEC) sb) sbp = sres,
      generalize HERES:selectop irsem_exec (cast (by rw HCSZONE') ec) ecp
                      ea_sz ea eap (cast (by rw HSZEQ) eb) ebp = eres,
      rw HSRES at HOSS',
      rw HERES at HOSE',
      cases eres with eresv eresp,
      cases sres with sresv sresp,
      right,
      apply exists.intro (irstate.updatereg irsem_smt ss lhsname (valty.ival sa_sz sresv sresp)),
      apply exists.intro (irstate.updatereg irsem_exec se lhsname (valty.ival ea_sz eresv eresp)),
      split, assumption,
      split, assumption,
      apply irstate.updatereg_equiv,
      { intros HNOUB,
        have HVAEQ := HVAEQ HNOUB,
        have HVBEQ := HVBEQ HNOUB,
        have HVCEQ := HVCEQ HNOUB,
        apply selectop_equiv, -- HERE!
        { apply HSTEQ },
        { apply val_equiv_rwsize2',
          apply HCSZONE, apply HCSZONE', apply HVCEQ },
        { apply HVAEQ },
        { apply val_equiv_rwsize2',
          rw HSZDEC, rw HSZEQ, apply HVBEQ },
        { assumption },
        { rw HSRES },
        { rw HERES }
      },
      simp,
      assumption,
      assumption
    }
  }
end

lemma unaryop_step_both: ∀ (ss:irstate_smt) (se:irstate_exec) (lhsname:string)
    (ucode:uopcode) (oss':option irstate_smt) (ose':option irstate_exec) (toisz:nat)
    (sa:valty_smt) (ea:valty_exec)
    (HSTEQ: irstate_equiv ss se)
    (HVAEQ: has_no_ub se = tt → val_equiv sa ea)
    (HASZEQ: equals_size sa ea = tt)
    (HOSS': oss' = step_unaryop irsem_smt sa ucode toisz ss lhsname)
    (HOSE': ose' = step_unaryop irsem_exec ea ucode toisz se lhsname),
  none_or_some oss' ose' (λ ss' se', irstate_equiv ss' se')
:= begin
  intros,
  cases sa with sa_sz sa sap,
  cases ea with ea_sz ea eap,
  simp at HASZEQ,
  unfold step_unaryop at HOSS' HOSE',
  destruct ucode,
  { -- freeze : not implemented yet
    intros HFREEZE, subst HFREEZE,
    unfold step_unaryop._match_1 at *,
    left, split; assumption
  },
  any_goals { -- cast operations
    intros HCAST, rw HCAST at *,
    have HTOISZDEC:decidable (toisz > 0), apply_instance,
    cases HTOISZDEC,
    { -- condition bitsize is not 1 -> stuck
      unfold step_unaryop._match_1 at *,
      simp [HTOISZDEC] at *,
      left, split; assumption
    },{
      generalize HSRES:castop irsem_smt sa_sz ucode sa sap ⟨toisz, HTOISZDEC⟩ = sres,
      generalize HERES:castop irsem_exec ea_sz ucode ea eap ⟨toisz, HTOISZDEC⟩ = eres,
      rw HCAST at HSRES HERES,
      unfold step_unaryop._match_1 at *,
      simp [HTOISZDEC] at HOSE',
      simp [HTOISZDEC] at HOSS',
      rw HSRES at HOSS',
      rw HERES at HOSE',
      cases eres with eresv eresp,
      cases sres with sresv sresp,
      right,
      apply exists.intro (irstate.updatereg irsem_smt ss lhsname (valty.ival ⟨toisz, _⟩ sresv sresp)),
      apply exists.intro (irstate.updatereg irsem_exec se lhsname (valty.ival ⟨toisz, _⟩ eresv eresp)),
      split, assumption,
      split, assumption,
      apply irstate.updatereg_equiv,
      { intros HNOUB,
        have HVAEQ := HVAEQ HNOUB,
        apply castop_equiv, -- HERE!
        { assumption },
        { assumption },
        { simp },
        { rw HSRES },
        { rw HERES }
      },
      simp,
      assumption
    }
  }
end

meta def step_returns_none (H:name) : tactic unit :=
  `[rw H at *, unfold option.bind at HOSS' HOSE', left, split; assumption ]

theorem step_both_prf: step_both :=
begin
  unfold step_both,
  intros,
  cases i,
  case instruction.binop : retty lhs bopc flags op1 op2 {
    cases lhs,
    cases lhs,

    unfold step_exe at HOSS' HOSE',
    generalize HEVOP1: get_value irsem_exec se op1 retty = evop1,
    generalize HSVOP1: get_value irsem_smt ss op1 retty = svop1,
    generalize HEVOP2: get_value irsem_exec se op2 retty = evop2,
    generalize HSVOP2: get_value irsem_smt ss op2 retty = svop2,
    rw [HEVOP1, HEVOP2] at HOSE',
    rw [HSVOP1, HSVOP2] at HOSS',

    unfold has_bind.bind at *,
    cases evop1 with ev1,
    { -- op1 is none.
      -- op1(smt) sould be none, too
      have H: svop1 = none, {
        apply get_value_none,
        assumption, rw HSVOP1, rw HEVOP1
      },
      step_returns_none `H
    },
    { -- op1 is some value
      -- now op2!
      have H1: (∃ sv1', svop1 = some sv1' ∧
                equals_size sv1' ev1 = tt ∧
                (has_no_ub se = tt → val_equiv sv1' ev1)), {
        apply get_value_some,
        assumption,
        rw HSVOP1, rw HEVOP1
      },
      cases H1 with sv1 H1 _,
      cases H1 with H11 H1,
      cases H1 with HSZ1 H1,
      rw H11 at *,
      clear H11, -- 'svop1 = some (sv1, sp1)' is unnecessary anymore.

      cases evop2 with ev2,
      { -- op2 is none.
        -- op2(smt) sould be none, too
        have H: svop2 = none, {
          apply get_value_none,
          assumption, rw HSVOP2, rw HEVOP2
        },
        step_returns_none `H
      },
      {
        have H2: (∃ sv2', svop2 = some sv2' ∧
                  equals_size sv2' ev2 = tt ∧
                  (has_no_ub se = tt → val_equiv sv2' ev2)), {
          apply get_value_some,
          assumption,
          rw HSVOP2, rw HEVOP2
        },
        cases H2 with sv2 H2 _,
        cases H2 with H21 H2,
        cases H2 with HSZ2 H2,
        rw H21 at *,
        clear H21, -- 'svop1 = some (sv1, sp1)' is unnecessary anymore.

        unfold option.bind at HOSS' HOSE',
        apply bop_step_both,
        { apply HSTEQ },
        { apply H1 },
        { apply H2 },
        { assumption },
        { assumption },
        apply HOSS',
        apply HOSE'
      }
    }
  },
  case instruction.icmpop : opty lhs cond op1 op2 {
    cases lhs,
    cases lhs,

    unfold step_exe at HOSS' HOSE',
    generalize HEVOP1: get_value irsem_exec se op1 opty = evop1,
    generalize HSVOP1: get_value irsem_smt ss op1 opty = svop1,
    generalize HEVOP2: get_value irsem_exec se op2 opty = evop2,
    generalize HSVOP2: get_value irsem_smt ss op2 opty = svop2,
    rw [HEVOP1, HEVOP2] at HOSE',
    rw [HSVOP1, HSVOP2] at HOSS',

    unfold has_bind.bind at *,
    cases evop1 with ev1,
    { -- op1 is none.
      -- op1(smt) sould be none, too
      have H: svop1 = none, {
        apply get_value_none,
        assumption, rw HSVOP1, rw HEVOP1
      },
      step_returns_none `H
    },
    { -- op1 is some value
      -- now op2!
      have H1: (∃ sv1', svop1 = some sv1' ∧
                equals_size sv1' ev1 = tt ∧
                (has_no_ub se = tt → val_equiv sv1' ev1)), {
        apply get_value_some,
        assumption,
        rw HSVOP1, rw HEVOP1
      },
      cases H1 with sv1 H1 _,
      cases H1 with H11 H1,
      cases H1 with HSZ1 H1,
      rw H11 at *,
      clear H11, -- 'svop1 = some (sv1, sp1)' is unnecessary anymore.

      cases evop2 with ev2,
      { -- op2 is none.
        -- op2(smt) sould be none, too
        have H: svop2 = none, {
          apply get_value_none,
          assumption, rw HSVOP2, rw HEVOP2
        },
        step_returns_none `Hs
      },
      {
        have H2: (∃ sv2', svop2 = some sv2' ∧
                  equals_size sv2' ev2 = tt ∧
                  (has_no_ub se = tt → val_equiv sv2' ev2)), {
          apply get_value_some,
          assumption,
          rw HSVOP2, rw HEVOP2
        },
        cases H2 with sv2 H2 _,
        cases H2 with H21 H2,
        cases H2 with HSZ2 H2,
        rw H21 at *,
        clear H21, -- 'svop1 = some (sv1, sp1)' is unnecessary anymore.

        unfold option.bind at HOSS' HOSE',
        apply icmpop_step_both,
        { apply HSTEQ },
        { apply H1 },
        { apply H2 },
        { assumption },
        { assumption },
        apply HOSS',
        apply HOSE'
      }
    }
  },
  case instruction.selectop : lhs condty cond opty op1 op2 {
    cases lhs,
    cases lhs,

    unfold step_exe at HOSS' HOSE',
    generalize HSVCNDOP: get_value irsem_smt ss cond condty = svcondop,
    generalize HEVCNDOP: get_value irsem_exec se cond condty = evcondop,
    generalize HEVOP1: get_value irsem_exec se op1 opty = evop1,
    generalize HSVOP1: get_value irsem_smt ss op1 opty = svop1,
    generalize HEVOP2: get_value irsem_exec se op2 opty = evop2,
    generalize HSVOP2: get_value irsem_smt ss op2 opty = svop2,
    rw [HEVCNDOP, HEVOP1, HEVOP2] at HOSE',
    rw [HSVCNDOP, HSVOP1, HSVOP2] at HOSS',

    unfold has_bind.bind at *,
    cases evcondop with ecv,
    { -- conditional op is none.
      -- conditional op(smt) sould be none, too
      have H: svcondop = none, {
        apply get_value_none,
        assumption, rw HSVCNDOP, rw HEVCNDOP
      },
      step_returns_none `H
    },
    { -- conditioanl op is some value.
      -- now op1!
      have HC: (∃ scv', svcondop = some scv' ∧
                equals_size scv' ecv = tt ∧
                (has_no_ub se = tt → val_equiv scv' ecv)), {
        apply get_value_some,
        assumption,
        rw HSVCNDOP, rw HEVCNDOP
      },
      cases HC with scv HC _,
      cases HC with HC1 HC,
      cases HC with HSZC HC,
      rw HC1 at *,
      clear HC1, -- 'svop1 = some (sv1, sp1)' is unnecessary anymore.
      
      cases evop1 with ev1,
      { -- op1 is none.
        -- op1(smt) sould be none, too
        have H: svop1 = none, {
          apply get_value_none,
          assumption, rw HSVOP1, rw HEVOP1
        },
        step_returns_none `H
      },
      { -- op1 is some value
        -- now op2!
        have H1: (∃ sv1', svop1 = some sv1' ∧
                  equals_size sv1' ev1 = tt ∧
                  (has_no_ub se = tt → val_equiv sv1' ev1)), {
          apply get_value_some,
          assumption,
          rw HSVOP1, rw HEVOP1
        },
        cases H1 with sv1 H1 _,
        cases H1 with H11 H1,
        cases H1 with HSZ1 H1,
        rw H11 at *,
        clear H11, -- 'svop1 = some (sv1, sp1)' is unnecessary anymore.

        cases evop2 with ev2,
        { -- op2 is none.
          -- op2(smt) sould be none, too
          have H: svop2 = none, {
            apply get_value_none,
            assumption, rw HSVOP2, rw HEVOP2
          },
          step_returns_none `H
        },
        {
          have H2: (∃ sv2', svop2 = some sv2' ∧
                    equals_size sv2' ev2 = tt ∧
                    (has_no_ub se = tt → val_equiv sv2' ev2)), {
            apply get_value_some,
            assumption,
            rw HSVOP2, rw HEVOP2
          },
          cases H2 with sv2 H2 _,
          cases H2 with H21 H2,
          cases H2 with HSZ2 H2,
          rw H21 at *,
          clear H21, -- 'svop1 = some (sv1, sp1)' is unnecessary anymore.

          unfold option.bind at HOSS' HOSE',
          apply selectop_step_both,
          { apply HSTEQ },
          { apply H1 },
          { apply H2 },
          { apply HC },
          { assumption },
          { assumption },
          { assumption },
          apply HOSS',
          apply HOSE'
        }
      }
    }
  },
  case instruction.unaryop : lhs ucode fromty op toty {
    cases lhs,
    cases lhs,

    cases toty,
    case ty.int : toisz {
      unfold step_exe at HOSS' HOSE',
      generalize HEVOP: get_value irsem_exec se op fromty = evop,
      generalize HSVOP: get_value irsem_smt ss op fromty = svop,
      rw HEVOP at HOSE',
      rw HSVOP at HOSS',

      unfold has_bind.bind at *,
      cases evop with ev,
      { -- evop is none -> svop is also none!
        have H: svop = none, {
          apply get_value_none,
          assumption, rw HSVOP, rw HEVOP
        },
        step_returns_none `H
      },
      { -- evop is something
        have H: (∃ sv', svop = some sv' ∧
                  equals_size sv' ev = tt ∧
                  (has_no_ub se = tt → val_equiv sv' ev)), {
          apply get_value_some,
          assumption,
          rw HSVOP, rw HEVOP
        },
        cases H with sv H _,
        cases H with H1 H,
        cases H with HSZ H,
        rw H1 at *,
        clear H1,
        -- now svop is something too.

        unfold option.bind at HOSS' HOSE',
        apply unaryop_step_both,
        { apply HSTEQ },
        { apply H },
        { assumption },
        apply HOSS',
        apply HOSE'
      }
    },
    {
      unfold step_exe at HOSS' HOSE',
      left, split; assumption
    }
  }
end

lemma bigstep_unroll_none_smt: ∀ s (i:instruction)
    (l:list instruction)
    (H: none = irsem.step_exe irsem_smt s i),
  irsem.bigstep_exe irsem_smt s { insts := i::l } = none
:= begin
  intros,
  unfold irsem.bigstep_exe,
  simp,
  unfold bigstep_exe._match_1,
  rw ← H,
  induction l, refl, simp, assumption
end

lemma bigstep_unroll_none_exec: ∀ s (i:instruction)
    (l:list instruction)
    (H: none = irsem.step_exe irsem_exec s i),
  irsem.bigstep_exe irsem_exec s { insts := i::l } = none
:= begin
  intros,
  unfold irsem.bigstep_exe,
  simp,
  unfold bigstep_exe._match_1,
  rw ← H,
  induction l, refl, simp, assumption
end

lemma bigstep_unroll_some_smt: ∀ s s' (i:instruction)
    (l:list instruction)
    (H: some s' = irsem.step_exe irsem_smt s i),
  irsem.bigstep_exe irsem_smt s { insts := i::l } =
    irsem.bigstep_exe irsem_smt s' { insts := l }
:= begin
  intros,
  unfold bigstep_exe,
  simp,
  unfold bigstep_exe._match_1,
  rw H
end

lemma bigstep_unroll_some_exec: ∀ s s' (i:instruction)
    (l:list instruction)
    (H: some s' = irsem.step_exe irsem_exec s i),
  irsem.bigstep_exe irsem_exec s { insts := i::l } =
    irsem.bigstep_exe irsem_exec s' { insts := l }
:= begin
  intros,
  unfold bigstep_exe,
  simp,
  unfold bigstep_exe._match_1,
  rw H
end


lemma bigstep_both_equiv: ∀ {ss:irstate_smt} {se:irstate_exec} {p:program}
    {oss':option irstate_smt} {ose':option irstate_exec}
    (HSTEQ: irstate_equiv ss se)
    (HOSS': oss' = bigstep_exe irsem_smt ss p)
    (HOSE': ose' = bigstep_exe irsem_exec se p),
  none_or_some oss' ose' (λ ss' se', irstate_equiv ss' se')
:= begin
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
    have HENC0 : none_or_some oss0 ose0 (λ ss0 se0, irstate_equiv ss0 se0),
    {
      apply step_both_prf,
      assumption, rw HSS, rw HSE
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

end spec
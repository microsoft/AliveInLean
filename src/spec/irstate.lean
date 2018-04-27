import .spec
import .lemmas
import ..irsem


namespace spec

open irsem
/-
 - Lemmas about regfile.
 -/

-- Induction principle of regfile.
lemma regfile.induction: ∀ {sem} {P: regfile sem → Prop}
    {HP0: P (@regfile.empty sem)}
    {HPU: ∀ rf, P rf → ∀ n v, P (regfile.update sem rf n v)},
  ∀ rf, P rf
:= begin
  intros,
  induction rf,
  { apply HP0 },
  {
    cases rf_hd,
    unfold regfile.update at HPU,
    apply HPU, assumption
  }
end

-- regfile.get returns none on regfile.empty
lemma regfile.empty_get_none: ∀ {sem} rname,
  regfile.get sem (regfile.empty sem) rname = none
:= begin
  intros,
  unfold regfile.empty,
  unfold regfile.get,
  simp,
  unfold regfile.get._match_1
end

lemma regfile.empty_apply_empty: ∀ {sem} f,
  regfile.apply_to_values sem (regfile.empty sem) f = regfile.empty sem
:= begin
  intros,
  unfold regfile.empty,
  refl
end

-- regfile.get returns the value which is updated just before
-- if rname = rname2
lemma regfile.update_get_match: ∀ {sem} (rname rname2:string) vp rf
    (Hnameeq: rname2 = rname),
  regfile.get sem (regfile.update sem rf rname vp) rname2 = some vp
:= begin
  intros,
  unfold regfile.get,
  unfold regfile.update,
  rw list.filter_cons_of_pos,
  { unfold regfile.get._match_1 },
  { simp, assumption }
end

-- Updating a register file does not affect the result
-- of regfile.get if rname ≠ rname2
lemma regfile.update_get_nomatch: ∀ {sem} (rname rname2:string) vp rf
    (Hnameeq: rname2 ≠ rname),
  regfile.get sem (regfile.update sem rf rname vp) rname2 =
  regfile.get sem rf rname2
:= begin
  intros,
  unfold regfile.get,
  unfold regfile.update,
  rw list.filter_cons_of_neg,
  { simp, assumption },
end

lemma regfile.regnames_empty: ∀ {sem} n,
  n ∉ regfile.regnames sem (regfile.empty sem)
:= begin
  intros,
  unfold regfile.regnames,
  unfold regfile.empty,
  simp
end

lemma regfile.reg_in_regnames_update: ∀ {sem} rf n n' v 
    (H: n ∈ regfile.regnames sem rf),
  n ∈ regfile.regnames sem (regfile.update sem rf n' v)
:= begin
  intros,
  unfold regfile.update,
  unfold regfile.regnames at *,
  simp,
  right, apply H
end

lemma regfile.reg_in_regnames_update2: ∀ {sem} rf n v,
  n ∈ regfile.regnames sem (regfile.update sem rf n v)
:= begin
  intros,
  unfold regfile.update,
  unfold regfile.regnames at *,
  simp
end

lemma regfile.reg_in_regnames_update3: ∀ {sem} rf n n' v 
    (H: n ∈ regfile.regnames sem (regfile.update sem rf n' v))
    (HNEQ: n ≠ n'),
  n ∈ regfile.regnames sem rf
:= begin
  intros,
  unfold regfile.update at H,
  unfold regfile.regnames at *,
  simp at *,
  cases H,
  { exfalso, apply HNEQ, assumption },
  assumption
end

lemma regfile.reg_notin_regnames_get_none: ∀ {sem} (rname:string) (f:regfile sem),
  regfile.get sem f rname = none ↔ rname ∉ regfile.regnames sem f
:= begin
  intros,
  split,
  {
    intros H,
    induction f,
    { unfold regfile.regnames, simp },
    {
      unfold regfile.get at H,
      unfold regfile.regnames,
      cases f_hd with n1 v1, unfold list.filter at H,
      simp,
      have H0: decidable (n1 = rname), apply_instance,
      cases H0,
      {
        rw if_neg at H,
        { intros H1,
          cases H1,
          { rw H1 at H0, apply H0, refl },
          { apply f_ih, apply H, apply H1 }
        },
        {
          simp, apply neq_symm, apply H0
        }
      },
      {
        rw if_pos at H,
        unfold regfile.get._match_1 at H, cases H,
        simp, rw H0
      }
    }
  },
  {
    intros H,
    induction f,
    {
      unfold regfile.get,
      simp, unfold regfile.get._match_1
    },
    {
      unfold regfile.regnames at H,
      simp at H,
      rw ← list.mem_cons_iff at H,
      rw list.notmem_and at H,
      unfold regfile.get,
      have H: decidable (f_hd.fst = rname), apply_instance,
      cases H,
      { -- first element is not rname
        unfold list.filter,
        rw if_neg, apply f_ih,
        cases H, apply H_right,
        intros H', rw H' at H_1, apply H_1, refl
      },
      {
        cases H, rw H_1 at H_left, exfalso, apply H_left, refl
      }
    }
  }
end

lemma regfile.reg_in_regnames_get_some: ∀ {sem} (rname:string) (f:regfile sem),
  (∃ v, regfile.get sem f rname = some v) ↔ rname ∈ regfile.regnames sem f
:= begin
  intros,
  split,
  {
    apply regfile.induction f,
    {
      intros H, cases H,
      rw regfile.empty_get_none at H_h,
      cases H_h
    },
    {
      intros s Hind n v H,
      have HN:decidable (n = rname), apply_instance,
      cases HN,
      {
        rw regfile.update_get_nomatch at H,
        have H := Hind H,
        apply regfile.reg_in_regnames_update, assumption,
        apply neq_symm, assumption
      },
      {
        rw HN,
        apply regfile.reg_in_regnames_update2
      }
    }
  },
  {
    apply regfile.induction f,
    { intros H, cases H },
    {
      intros rf Hind n v H,
      have HN:decidable (n = rname), apply_instance,
      cases HN,
      {
        rw regfile.update_get_nomatch,
        apply Hind,
        apply regfile.reg_in_regnames_update3,
        { apply H },
        any_goals { apply neq_symm, assumption },
      },
      {
        rw HN,
        apply exists.intro v,
        apply regfile.update_get_match, refl
      }
    }
  }
end

lemma regfile.apply_update_comm: ∀ {sem} f n v rf,
  regfile.apply_to_values sem (regfile.update sem rf n v) f =
    regfile.update sem (regfile.apply_to_values sem rf f) n (f v)
:= begin
  intros, unfold regfile.apply_to_values, unfold regfile.update, refl
end

-- Note: reverse direction does not hold!
lemma regfile.reg_apply_some: ∀ {sem} (rf:regfile sem) (f:valty sem → valty sem) v n
    (H:regfile.get sem rf n = some v),
  regfile.get sem (regfile.apply_to_values sem rf f) n = some (f v)
:= begin
  intros,
  revert H,
  apply regfile.induction rf,
  { intros H, rw regfile.empty_get_none at H, cases H },
  {
    intros rf Hind n1 v1 H,
    have HNAME: decidable(n1 = n), apply_instance,
    cases HNAME,
    {
      rw regfile.update_get_nomatch at H,
      have H' := Hind H,
      rw regfile.apply_update_comm,
      rw regfile.update_get_nomatch, assumption,
      any_goals { apply neq_symm, assumption }
    },
    {
      rw regfile.update_get_match at H,
      injection H, subst h_1,
      rw regfile.apply_update_comm,
      rw regfile.update_get_match,
      any_goals { rw HNAME }
    }
  }
end

lemma regfile.reg_apply_none: ∀ {sem} (rf:regfile sem) (f:valty sem → valty sem) n,
  regfile.get sem rf n = none ↔ regfile.get sem (regfile.apply_to_values sem rf f) n = none
:= begin
  intros,
  split,
  {
    apply regfile.induction rf,
    {
      intros H, rw regfile.empty_apply_empty, assumption
    },
    {
      intros rf Hind n1 v1 H,
      have HNAME: decidable(n1 = n), apply_instance,
      cases HNAME,
      {
        rw regfile.update_get_nomatch at H,
        have H' := Hind H,
        rw regfile.apply_update_comm,
        rw regfile.update_get_nomatch, assumption,
        any_goals { apply neq_symm, assumption }
      },
      {
        rw regfile.update_get_match at H,
        injection H, rw HNAME
      }
    }
  },
  {
    apply regfile.induction rf,
    {
      intros H, rw regfile.empty_apply_empty at H, assumption
    },
    {
      intros rf Hind n1 v1 H,
      have HNAME: decidable(n1 = n), apply_instance,
      cases HNAME,
      {
        rw regfile.apply_update_comm at H,
        rw regfile.update_get_nomatch at H,
        have H' := Hind H,
        rw regfile.update_get_nomatch, assumption,
        any_goals { apply neq_symm, assumption }
      },
      {
        rw regfile.apply_update_comm at H,
        rw regfile.update_get_match at H,
        injection H, rw HNAME
      }
    }
  }
end

lemma irstate.updatereg_getreg_match_smt: ∀ (rname rname2:string) v st
    (Hnameeq: rname2 = rname),
  irstate.getreg irsem_smt (irstate.updatereg irsem_smt st rname v) rname2 = some v
:= begin
  intros,
  unfold irstate.getreg,
  unfold irstate.updatereg,
  simp,
  apply regfile.update_get_match, assumption
end

lemma irstate.notin_regnames_getreg_smt: ∀ (rname:string) (s:irstate irsem_smt)
    (H:rname ∉ irstate.regnames irsem_smt s),
  irstate.getreg irsem_smt s rname = none
:= begin
  intros,
  unfold irstate.getreg,
  unfold irstate.regnames at *,
  cases s,
  simp,
  rw regfile.reg_notin_regnames_get_none,
  apply H
end

lemma irstate.getreg_diff_smt: ∀ ss (n1 n2:string) v
    (H1:  irstate.getreg irsem_smt ss n1 = none)
    (H2:  irstate.getreg irsem_smt ss n2 = some v),
  n1 ≠ n2
:= begin
  intros,
  intros HEQ,
  rw HEQ at H1,
  rw H1 at H2,
  cases H2
end

lemma irstate.updatereg_getreg_nomatch_smt: ∀ ss ss' (n1 n2:string) v v'
    (H1: irstate.getreg irsem_smt ss n1 = v)
    (H2: ss' = irstate.updatereg irsem_smt ss n2 v')
    (HDIFF:n1 ≠ n2),
  irstate.getreg irsem_smt ss' n1 = v
:= begin
  intros,
  rw H2,
  unfold irstate.getreg at *,
  unfold irstate.updatereg at *,
  simp,
  rw regfile.update_get_nomatch, assumption, assumption
end

lemma irstate.updatereg_getreg_nomatch_inv_smt: ∀ ss ss' (n1 n2:string) v v'
    (H1: irstate.getreg irsem_smt ss' n1 = v)
    (H2: ss' = irstate.updatereg irsem_smt ss n2 v')
    (HDIFF:n1 ≠ n2),
  irstate.getreg irsem_smt ss n1 = v
:= begin
  intros,
  rw H2 at H1,
  unfold irstate.getreg at *,
  unfold irstate.updatereg at *,
  simp at H1,
  rw regfile.update_get_nomatch at H1, assumption, assumption
end

lemma irstate.getreg_empty_none_smt: ∀ s n
    (H:irstate.regnames irsem_smt s = []),
  irstate.getreg irsem_smt s n = none
:= begin
  intros,
  cases s with ub rf,
  unfold irstate.regnames at H,
  unfold regfile.regnames at H,
  simp at H,
  have H' : rf = [],
  { apply list.map_nil, apply H },
  rw H', unfold irstate.getreg, unfold regfile.get, simp,
  delta regfile.get._match_1, simp
end

lemma irstate.getub_equiv: ∀ {ss:irstate_smt} {se:irstate_exec}
    {sret} {eret} (HSTEQ:irstate_equiv ss se)
    (HSSRET: sret = ss.getub irsem_smt)
    (HSERET: eret = se.getub irsem_exec),
  b_equiv sret eret
:= begin
  intros,
  cases HSTEQ,
  any_goals { -- irstate_equiv.noub
    unfold irstate.getub at HSSRET,
    unfold irstate.getub at HSERET,
    simp at HSSRET, simp at HSERET,
    subst HSSRET, subst HSERET, assumption
  }
end

lemma irstate.getub_updatereg_smt: ∀ (s:irstate irsem_smt) n v,
  irstate.getub irsem_smt (irstate.updatereg irsem_smt s n v) = irstate.getub irsem_smt s
:= begin
  intros,
  unfold irstate.updatereg,
  refl
end

lemma irstate.getreg_apply_some_smt: ∀ (s:irstate irsem_smt) (f:valty_smt → valty_smt) v n
    (H: irstate.getreg irsem_smt s n = some v),
  irstate.getreg irsem_smt (irstate.apply_to_values irsem_smt s f) n = some (f v)
:= begin
  intros,
  cases s,
  unfold irstate.apply_to_values,
  unfold irstate.getreg,
  apply regfile.reg_apply_some,
  apply H
end

lemma irstate.getreg_apply_none_smt: ∀ (s:irstate irsem_smt) (f:valty_smt → valty_smt) n,
  irstate.getreg irsem_smt s n = none ↔
  irstate.getreg irsem_smt (irstate.apply_to_values irsem_smt s f) n = none
:= begin
  intros,
  split,
  {
    intros H, cases s,
    unfold irstate.apply_to_values,
    unfold irstate.getreg,
    rw ← regfile.reg_apply_none,
    apply H
  },
  {
    intros H, cases s,
    unfold irstate.apply_to_values at H,
    unfold irstate.getreg,
    rw regfile.reg_apply_none,
    apply H
  }
end

lemma irstate.empty_apply_empty_smt: ∀ f,
  irstate.apply_to_values irsem_smt (irstate.empty irsem_smt) f = irstate.empty irsem_smt
:= begin
  intros,
  unfold irstate.empty,
  refl
end

lemma irstate.getub_apply_to_values: ∀ (s:irstate irsem_smt) f,
  irstate.getub irsem_smt (irstate.apply_to_values irsem_smt s f) =
    irstate.getub irsem_smt s
:= begin
  intros,
  unfold irstate.getub,
  unfold irstate.apply_to_values
end

lemma irstate.setub_apply_to_values: ∀ (s:irstate irsem_smt) f b,
  irstate.setub irsem_smt (irstate.apply_to_values irsem_smt s f) b =
    irstate.apply_to_values irsem_smt (irstate.setub irsem_smt s b) f
:= begin
  intros,
  unfold irstate.setub,
  unfold irstate.apply_to_values
end


end spec
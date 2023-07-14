-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import ..smtexpr
import ..bitvector
import .spec
--import .lemmas
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

-- An SMT bit-vector expression bv is closed if it does not have a (free) SMT variable.
--
-- (bvadd x 1) is not closed because it has a free variable 'x'
-- (bvadd 1 2) is closed because it does not have that.
--
-- We define closedness as follows: for any given mapping η, replacing the free
--   variable with any value (η⟦bv⟧) does not change the expression.
def closed_bv {sz:size} (bv:sbitvec sz) := ∀ (η:freevar.env), η⟦bv⟧ = bv

-- Same definition for boolean SMT expressions too.
def closed_b (b:sbool) := ∀ (η:freevar.env), η⟦b⟧ = b

def closed_valty (v:valty irsem_smt) := ∀ (η:freevar.env), η⟦v⟧ = v
def closed_regfile (rf:regfile irsem_smt) :=
  ∀ (η:freevar.env), rf.apply_to_values irsem_smt (η.replace_valty) = rf
def closed_irstate (ss:irstate irsem_smt) := ∀ (η:freevar.env), η⟦ss⟧ = ss


-- An interesting lemma about closedness:
-- Given an SMT bit-vector expression sb and LEAN bitvector value bv
--   and environment η,
-- If (1) η⟦sb⟧ is equivalent to bv, and (2) sb has no free variable,
-- then sb and bv are also equivalent.  
lemma closed_bv_equiv: ∀ {sz:size} (η:freevar.env)
    (sb:sbitvec sz) (bv:bitvector sz)
    (HEQ2:bv_equiv (η⟦sb⟧) bv)
    (HC:closed_bv sb),
  bv_equiv sb bv
:= begin
  intros,
  unfold closed_bv at HC,
  have HC' := HC η,
  rw HC' at HEQ2,
  assumption
end

lemma closed_b_equiv: ∀ (η:freevar.env)
    (sb:sbool) (b:bool)
    (HEQ:b_equiv (η⟦sb⟧) b)
    (HC:closed_b sb),
  b_equiv sb b
:= begin
  intros, unfold closed_b at HC, have HC := HC η, rw HC at HEQ, assumption
end

lemma closed_irstate_equiv: ∀ (η:freevar.env)
    (ss:irstate irsem_smt) (se:irstate irsem_exec)
    (HEQ:irstate_equiv (η⟦ss⟧) se)
    (HC:closed_irstate ss),
  irstate_equiv ss se
:= begin
  intros, unfold closed_irstate at HC, have HC := HC η, rw HC at HEQ, assumption
end

lemma closed_b_never_var: ∀ s, ¬ closed_b (sbool.var s)
:= begin
  intros,
  intro H,
  unfold closed_b at H,
  have H' := H (freevar.env.empty.add_b s tt),
  unfold env.add_b at H',
  unfold freevar.env.replace_sb at H',
  simp at H',
  cases H'
end

lemma closed_bv_never_var: ∀ sz s, ¬ closed_bv (sbitvec.var sz s)
:= begin
  intros,
  intro H,
  unfold closed_bv at H,
  have H' := H (freevar.env.empty.add_bv s 1),
  unfold env.add_bv at H',
  unfold freevar.env.replace_sbv at H',
  simp at H',
  cases H'
end

lemma closed_irstate_closed_ub: ∀ {η:freevar.env} {ss:irstate irsem_smt}
    (HC:closed_irstate (η⟦ss⟧)),
  closed_b (η⟦irstate.getub irsem_smt ss⟧)
:= begin
  intros,
  cases ss,
  unfold closed_irstate at HC,
  unfold closed_b,
  intros η',
  have HC := HC η',
  unfold freevar.env.replace at HC,
  rw irstate.getub_apply_to_values at HC,
  unfold irstate.getub at *,
  unfold irstate.setub at HC,
  unfold irstate.apply_to_values at HC,
  injection HC
end

lemma closed_irstate_split: ∀ ub rf,
  closed_irstate (ub, rf) ↔ closed_b ub ∧ closed_regfile rf
:= begin
  intros,
  unfold closed_irstate,
  unfold freevar.env.replace,
  unfold closed_b,
  unfold closed_regfile,
  unfold irstate.getub,
  unfold irstate.setub,
  unfold irstate.apply_to_values,
  simp,
  split,
  {
    intros H,
    split,
    any_goals {
      intros, have H' := H η, cases H',tauto
    }
  },
  {
    intros H,
    cases H,
    intros,
    rw [H_left, H_right],tauto
  }
end

lemma closed_regfile_empty: closed_regfile (regfile.empty irsem_smt)
:= begin
  unfold regfile.empty,
  unfold closed_regfile,
  intros, refl
end

lemma closed_irstate_empty: closed_irstate (irstate.empty irsem_smt)
:= begin
  unfold irstate.empty,
  unfold closed_irstate,
  intros, refl
end

-- This lemma says that, for example, since
-- {x |-> tt}[[x]] (which is simply tt) is closed
--                 where x is an SMT boolean variable,
-- {x |-> tt, n |-> v}[[x]] is also closed.
lemma closed_b_var_add: ∀ (η:freevar.env) (n:string) (v:bool) (s:string)
    (HC: closed_b (η⟦sbool.var s⟧)),
  closed_b ((env.add_b η n v)⟦sbool.var s⟧)
:= begin
  unfold freevar.env.replace_sb,
  unfold env.add_b,
  simp,
  intros,
  generalize Hb': (η.b s) = b',
  rw Hb' at *,
  -- LEAN is based on Calculus of Inductive Construction, which cannot prove
  -- excluded middle (∀x, P x \/ ¬ P x) in general. (If you prove it, then I bet
  -- you will be really famous)
  -- However, if P is decidable (meaning that it has a concrete computing function
  -- that yields either true or false), then now you can use excluded middle.
  have Heq: decidable (s = n),
  { apply_instance }, -- Prove that there exists the computing function for s = n
  { cases Heq,
    { rw if_neg, assumption, assumption },
    {
      rw if_pos,
      unfold env.replace_sb._match_1 at *,
      cases v; unfold closed_b; intros; refl,
      assumption
    }
  }
end

lemma closed_b_var_add2: ∀ (η:freevar.env) (v:bool) (s:string),
  closed_b ((η.add_b s v)⟦sbool.var s⟧)
:= begin
  unfold env.add_b,
  unfold freevar.env.replace_sb,
  simp,
  intros,
  generalize Hb': (η.b s) = b',
  unfold closed_b,
  intros, cases v, refl, refl
end

-- This lemma is similar to closed_b_var_add
lemma closed_bv_var_add: ∀ (η:freevar.env) sz (n:string) v (s:string)
    (HC: closed_bv (η⟦sbitvec.var sz s⟧)),
  closed_bv ((env.add_bv η n v)⟦sbitvec.var sz s⟧)
:= begin
  unfold freevar.env.replace_sbv,
  unfold env.add_bv,
  simp,
  intros,
  generalize Hb': (η.b s) = b',
  rw Hb' at *,
  have Heq: decidable (s = n), apply_instance,
  cases Heq,
  { rw if_neg, assumption, assumption },
  {
    rw if_pos,
    unfold env.replace_sbv._match_1 at *,
    unfold closed_bv,
    cases v,
    any_goals {
      unfold sbitvec.of_int; intros;
      unfold freevar.env.replace_sbv
    },
    assumption
  }
end

lemma closed_bv_var_add2: ∀ (η:freevar.env) sz v (s:string),
  closed_bv ((η.add_bv s v)⟦sbitvec.var sz s⟧)
:= begin
  unfold env.add_bv,
  intros,
  generalize Hb': (η.b s) = b',
  unfold closed_bv,
  intros, cases v;
  unfold freevar.env.replace_sbv; simp,
  { unfold sbitvec.of_int, unfold env.replace_sbv },
  { unfold sbitvec.of_int, unfold env.replace_sbv },
end

lemma ival_closed: ∀ sz vn pn (η:freevar.env) z b,
  closed_valty (((η.add_bv vn z).add_b pn b)
    ⟦irsem.valty.ival sz (sbitvec.var sz vn) (sbool.var pn)⟧)
:= begin
  intros,
  unfold closed_valty,
  intros,
  unfold env.add_b,
  unfold env.add_bv,
  simp,
  split,
  {
    cases z; unfold sbitvec.of_int;
    unfold freevar.env.replace_sbv
  },
  {
    rw env.replace_sb_of_bool
  }
end

lemma closed_ival_split: ∀ sz bv p,
  closed_valty (irsem.valty.ival sz bv p) ↔
  closed_b p ∧ closed_bv bv
:= begin
  intros,
  unfold closed_valty,
  split,
  {
    intros H,
    unfold freevar.env.replace_valty at H,
    split,
    {
      unfold closed_b,
      intros,
      have H' := H η,
      injection H'
    },
    {
      unfold closed_bv,
      intros,
      have H' := H η,
      injection H',
      apply eq_of_heq, assumption
    }
  },
  {
    intros H,
    cases H,
    intros,
    unfold freevar.env.replace_valty,
    rw H_left,
    rw H_right
  }
end

lemma closed_regfile_update_split: ∀ {rf:regfile irsem_smt} {n} {v},
  closed_regfile (regfile.update irsem_smt rf n v)
  ↔ closed_regfile rf ∧ closed_valty v
:= begin
  intros,
  unfold regfile.update,
  unfold closed_valty,
  unfold closed_regfile,
  split,
  {
    intros HC,
    unfold regfile.apply_to_values at *,
    simp at HC,
    split,
    { intros, have HC := HC η, injection HC },
    { intros, have HC := HC η, injection HC, injection h_1 }
  },
  {
    intros HC η,
    cases HC with HC1 HC2,
    have HC1 := HC1 η,
    have HC2 := HC2 η,
    unfold regfile.apply_to_values at *,
    simp at *,
    rw HC1, rw HC2
  }
end



-- TODO 1: Merge closed_b_add_b and closed_bv_add_b into a single
-- theorem (I tried merging them
-- but it raised excessive memory consumption error.)
-- TODO 2: closed_b_add_b, closed_b_add_bv, closed_bv_add_b,
-- closed_bv_add_bv are very similar. Is there any good way
-- to merge all of them into single theorem 
lemma closed_b_add_b: ∀ {η s} n v
    (HC: closed_b (η⟦s⟧)),
  closed_b ((η.add_b n v)⟦s⟧)
:= begin
  intros,
  revert s,
  apply sbool.induction
      (λ s, closed_b (η⟦s⟧) → closed_b ((η.add_b n v)⟦s⟧))
      (λ {sz} sb, closed_bv (η⟦sb⟧) → closed_bv ((η.add_b n v)⟦sb⟧)),
  { unfold freevar.env.replace_sb,
    intros, assumption },
  { unfold freevar.env.replace_sb,
    intros, assumption },
  {
    intros,
    apply closed_b_var_add; assumption
  },
  -- I didn't use any_goals because it raises excessive
  -- memory consumptions.
  { unfold closed_b, intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0, rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  { unfold closed_b, intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0, rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  { unfold closed_b, intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0, rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  { unfold closed_b, intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0, rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  { unfold closed_b, intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0, rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  {
    unfold closed_b,
    intros b1 b2 b3 IH1 IH2 IH3 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH1, rw IH2, rw IH3,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  {
    unfold closed_b,
    intros b IH H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  any_goals {
    unfold closed_b, unfold closed_bv,
    intros sz v1 v2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', apply eq_of_heq, assumption }
  },
  {
    unfold closed_bv,
    intros b IH H0 η',
    unfold freevar.env.replace_sbv,
    done
  },
  {
    intros,
    generalize Hb': (η.bv n_1) = b',
    unfold env.add_b,
    unfold freevar.env.replace_sbv at *,
    rw Hb' at *,
    cases b'; unfold env.replace_sbv._match_1 at *; assumption
  },
  any_goals {
    unfold closed_bv,
    intros sz v1 v2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sbv,
    unfold freevar.env.replace_sbv at H0,
    rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  any_goals {
    unfold closed_bv,
    intros sz v sz' IH H0 η',
    unfold freevar.env.replace_sbv,
    unfold freevar.env.replace_sbv at H0,
    rw IH,
    { intros η'', have H0' := H0 η'', injection H0', apply eq_of_heq, assumption }
  },
  {
    intros sz sz' v h l IH1 IH2 H0 η',
    unfold freevar.env.replace_sbv at *,
    rw IH2,
    unfold closed_bv at *,
    { intros η'', have H0' := H0 η'', unfold freevar.env.replace_sbv at H0',
      injection H0', apply eq_of_heq, assumption }
  },
  {
    unfold closed_bv,
    intros sz b v1 v2 IH1 IH2 IH3 H0 η',
    unfold freevar.env.replace_sbv at *,
    rw IH1, rw IH2, rw IH3,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  }
end

lemma closed_b_add_bv: ∀ {η s} n v
    (HC: closed_b (η⟦s⟧)),
  closed_b ((η.add_bv n v)⟦s⟧)
:= begin
  intros,
  revert s,
  apply sbool.induction
      (λ s, closed_b (η⟦s⟧) → closed_b ((η.add_bv n v)⟦s⟧))
      (λ {sz} sb, closed_bv (η⟦sb⟧) → closed_bv ((η.add_bv n v)⟦sb⟧)),
  { unfold freevar.env.replace_sb,
    intros, assumption },
  { unfold freevar.env.replace_sb,
    intros, assumption },
  { unfold freevar.env.replace_sb,
    intros, assumption },
  {
    intros b1 b2 IH1 IH2 H η,
    unfold env.add_bv at *,
    unfold closed_b at *,
    unfold freevar.env.replace_sb at *,
    simp at *,
    rw IH1, rw IH2,
    any_goals { split; refl },
    all_goals { intros η', have H' := H η', cases H'; assumption }
  },
  any_goals {
    unfold closed_b,
    intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  {
    unfold closed_b,
    intros b1 b2 b3 IH1 IH2 IH3 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH1, rw IH2, rw IH3,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  {
    unfold closed_b,
    intros b IH H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  any_goals {
    unfold closed_b, unfold closed_bv,
    intros sz v1 v2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', apply eq_of_heq, assumption }
  },
  {
    unfold closed_bv,
    intros b IH H0 η',
    unfold freevar.env.replace_sbv,
    done
  },
  {
    intros,
    apply closed_bv_var_add; assumption
  },
  any_goals {
    unfold closed_bv,
    intros sz v1 v2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sbv,
    unfold freevar.env.replace_sbv at H0,
    rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  any_goals {
    unfold closed_bv,
    intros sz v sz' IH H0 η',
    unfold freevar.env.replace_sbv,
    unfold freevar.env.replace_sbv at H0,
    rw IH,
    { intros η'', have H0' := H0 η'', injection H0', apply eq_of_heq, assumption }
  },
  {
    intros sz sz' v h l IH1 IH2 H0 η',
    unfold freevar.env.replace_sbv at *,
    rw IH2,
    unfold closed_bv at *,
    { intros η'', have H0' := H0 η'', unfold freevar.env.replace_sbv at H0',
      injection H0', apply eq_of_heq, assumption }
  },
  {
    unfold closed_bv,
    intros sz b v1 v2 IH1 IH2 IH3 H0 η',
    unfold freevar.env.replace_sbv at *,
    rw IH1, rw IH2, rw IH3,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  }
end

lemma closed_bv_add_b: ∀ {sz} {η} {s:sbitvec sz} n v
    (HC: closed_bv (η⟦s⟧)),
  closed_bv ((η.add_b n v)⟦s⟧)
:= begin
  intros,
  revert s,
  apply sbitvec.induction
      (λ s, closed_b (η⟦s⟧) → closed_b ((η.add_b n v)⟦s⟧))
      (λ {sz} sb, closed_bv (η⟦sb⟧) → closed_bv ((η.add_b n v)⟦sb⟧)),
  { unfold freevar.env.replace_sb,
    intros, assumption },
  { unfold freevar.env.replace_sb,
    intros, assumption },
  {
    intros,
    apply closed_b_var_add; assumption
  },
  -- I didn't use any_goals because it raises excessive
  -- memory consumptions.
  { unfold closed_b, intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0, rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  { unfold closed_b, intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0, rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  { unfold closed_b, intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0, rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  { unfold closed_b, intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0, rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  { unfold closed_b, intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0, rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  {
    unfold closed_b,
    intros b1 b2 b3 IH1 IH2 IH3 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH1, rw IH2, rw IH3,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  {
    unfold closed_b,
    intros b IH H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  any_goals {
    unfold closed_b, unfold closed_bv,
    intros sz v1 v2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', apply eq_of_heq, assumption }
  },
  {
    unfold closed_bv,
    intros b IH H0 η',
    unfold freevar.env.replace_sbv,
    done
  },
  {
    intros,
    generalize Hb': (η.bv n_1) = b',
    unfold env.add_b,
    unfold freevar.env.replace_sbv at *,
    rw Hb' at *,
    cases b'; unfold env.replace_sbv._match_1 at *; assumption
  },
  any_goals {
    unfold closed_bv,
    intros sz v1 v2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sbv,
    unfold freevar.env.replace_sbv at H0,
    rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  any_goals {
    unfold closed_bv,
    intros sz v sz' IH H0 η',
    unfold freevar.env.replace_sbv,
    unfold freevar.env.replace_sbv at H0,
    rw IH,
    { intros η'', have H0' := H0 η'', injection H0', apply eq_of_heq, assumption }
  },
  {
    intros sz sz' v h l IH1 IH2 H0 η',
    unfold freevar.env.replace_sbv at *,
    rw IH2,
    unfold closed_bv at *,
    { intros η'', have H0' := H0 η'', unfold freevar.env.replace_sbv at H0',
      injection H0', apply eq_of_heq, assumption }
  },
  {
    unfold closed_bv,
    intros sz b v1 v2 IH1 IH2 IH3 H0 η',
    unfold freevar.env.replace_sbv at *,
    rw IH1, rw IH2, rw IH3,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  }
end

lemma closed_bv_add_bv: ∀ {sz} {η} {s:sbitvec sz} n v
    (HC: closed_bv (η⟦s⟧)),
  closed_bv ((η.add_bv n v)⟦s⟧)
:= begin
  intros,
  revert s,
  apply sbitvec.induction
      (λ s, closed_b (η⟦s⟧) → closed_b ((η.add_bv n v)⟦s⟧))
      (λ {sz} sb, closed_bv (η⟦sb⟧) → closed_bv ((η.add_bv n v)⟦sb⟧)),
  { unfold freevar.env.replace_sb,
    intros, assumption },
  { unfold freevar.env.replace_sb,
    intros, assumption },
  { unfold freevar.env.replace_sb,
    intros, assumption },
  {
    intros b1 b2 IH1 IH2 H η,
    unfold env.add_bv at *,
    unfold closed_b at *,
    unfold freevar.env.replace_sb at *,
    simp at *,
    rw IH1, rw IH2,
    any_goals { split; refl },
    all_goals { intros η', have H' := H η', cases H'; assumption }
  },
  any_goals {
    unfold closed_b,
    intros b1 b2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  {
    unfold closed_b,
    intros b1 b2 b3 IH1 IH2 IH3 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH1, rw IH2, rw IH3,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  {
    unfold closed_b,
    intros b IH H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  any_goals {
    unfold closed_b, unfold closed_bv,
    intros sz v1 v2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sb,
    unfold freevar.env.replace_sb at H0,
    rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', apply eq_of_heq, assumption }
  },
  {
    unfold closed_bv,
    intros b IH H0 η',
    unfold freevar.env.replace_sbv,
    done
  },
  {
    intros,
    apply closed_bv_var_add; assumption
  },
  any_goals {
    unfold closed_bv,
    intros sz v1 v2 IH1 IH2 H0 η',
    unfold freevar.env.replace_sbv,
    unfold freevar.env.replace_sbv at H0,
    rw IH1, rw IH2,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  },
  any_goals {
    unfold closed_bv,
    intros sz v sz' IH H0 η',
    unfold freevar.env.replace_sbv,
    unfold freevar.env.replace_sbv at H0,
    rw IH,
    { intros η'', have H0' := H0 η'', injection H0', apply eq_of_heq, assumption }
  },
  {
    intros sz sz' v h l IH1 IH2 H0 η',
    unfold freevar.env.replace_sbv at *,
    rw IH2,
    unfold closed_bv at *,
    { intros η'', have H0' := H0 η'', unfold freevar.env.replace_sbv at H0',
      injection H0', apply eq_of_heq, assumption }
  },
  {
    unfold closed_bv,
    intros sz b v1 v2 IH1 IH2 IH3 H0 η',
    unfold freevar.env.replace_sbv at *,
    rw IH1, rw IH2, rw IH3,
    all_goals { intros η'', have H0' := H0 η'', injection H0', done }
  }
end

end spec
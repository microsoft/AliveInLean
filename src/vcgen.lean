-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import .lang
import .irsem
import .irsem_exec
import .irsem_smt
import .freevar
import smt2.syntax
import smt2.builder

namespace vcgen

open irsem
open smt2
open smt2.builder

-- An emitter that translates value, poison, ub into SMT terms.
structure emitter (sem:irsem) :=
  (val_f: sem.valty → term)
  (poison_f: sem.valty → term)
  (bool_f: sem.boolty → term)

meta def emit_smt (p:program)
  (freevars:list (string × ty)) (init_smt_st: irstate irsem_smt)
  (final_exec_st:irstate irsem_exec)
  (final_smt_st:irstate irsem_smt)
  (exec_emit:emitter irsem_exec) (smt_emit:emitter irsem_smt)
  : format :=
  let b:builder unit :=
    -- Let's show that Behavior(EXEC) ∈ Behavior(SMT)!
    -- In nondeterministic semantics, SMT may encode
    -- many possible choices, but exec will only have one execution result.
    --   First of all, (ub ∈ UB_smt) must hold.
    -- ub is a single bool that says whether UB happened in the execution.
    -- UB_smt is a SMT term, and it will encode a subset of {tt, ff}.
    --   Second, for all register r, poison(r) ∈ POISON_smt(r) must hold.
    -- poison(r) is a bool that says whether register r is poison
    -- or not. POISON_smt(r) is a SMT term.
    --   Third, if ub_yes ∉ UB_smt ∧ poison_yes ∉ POISON_smt(r),
    -- val(r) ∈ VAL_smt(r) must hold! ub_yes and poison_yes are
    -- constants saying that UB and poison are created.
    -- val(r) is a value after execution of the program.
    -- VAL_smt(r) is a SMT term that encodes a set of values that r may have
    -- in an execution.

    let reglist := irstate.regnames irsem_exec final_exec_st in
    -- Did execution raise UB?
    let ub_exec := exec_emit.bool_f (irstate.getub irsem_exec final_exec_st) in
    let ub_smt := smt_emit.bool_f (irstate.getub irsem_smt final_smt_st) in
    -- 'UB happened' constant
    let ub_yes := exec_emit.bool_f (irsem_exec.bbl.ff) in
    do
    -- First of all, declare freevars
    freevar.create_smt_declares freevars,
    -- Now generate assertions
    list.foldl (λ (bldr:builder unit) rdef:string,
        match (irstate.getreg irsem_exec final_exec_st rdef,
              irstate.getreg irsem_smt final_smt_st rdef) with
        | ((some val_exec), (some val_smt)) :=
          -- Prepare SMT terms
          let poison_exec := exec_emit.poison_f val_exec,
              poison_smt := smt_emit.poison_f val_smt,
              exval := exec_emit.val_f val_exec,
              smtval := smt_emit.val_f val_smt in
          let poison_yes := exec_emit.poison_f (irsem_exec.give_poison val_exec) in
          do bldr,
          -- Checks poison_exec(r) ∈ POISON_smt(r)
          assert (equals poison_exec poison_smt),
          -- Checks ub_yes ∉ UB_smt ∧ poison_yes(r) ∉ POISON_smt(r) →
          --        val(r) ∈ VAL_smt(r)
          assert (implies
              (and2 (not (equals ub_yes ub_smt))
                    (not (equals poison_yes poison_smt)))
              (equals exval smtval))
        | (_, _) := fail ("Fail to make assertion on register " ++ rdef)
        end)
        (assert (equals ub_exec ub_smt)) -- Checks ub_exec ∈ UB_smt first
        reglist,
    -- Add (check-sat)!
    check_sat in
  builder.to_format b


meta def emit_refine_smt (p1 p2:program) (freevars:list (string × ty))
  (refines:sbool) (smt_emit:emitter irsem_smt)
  : format :=
  let b:builder unit :=
    do
    -- First of all, declare freevars
    freevar.create_smt_declares freevars,
    -- Emit the refinement condition.
    assert (not (smt_emit.bool_f refines)),
    -- Add (check-sat)!
    check_sat in
  builder.to_format b

end vcgen
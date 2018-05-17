-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import system.io
import .smtexpr
import .smtcompile
import .spec.spec
import smt2.tactic

open tactic
open spec


namespace proptest

@[reducible]
meta def var := expr -- name and its type
meta def var.ty (v:var) :=
  match v with
  | (expr.local_const n1 n2 b itsty) := itsty
  | _ := v
  end
meta def var.setty (v:var) (newty:expr):var :=
  match v with
  | (expr.local_const n1 n2 b itsty) :=
    (expr.local_const n1 n2 b newty)
  | _ := v
  end
meta def tys (l:list var):list expr :=
  l.map (λ v, v.ty)

meta def print_detail: expr → nat → tactic unit
| (expr.local_const n1 n2 b itsty) icnt := do
  let indent := list.as_string (list.repeat ' ' icnt), 
  trace format!"{indent}(local_const {n1} {n2} _",
  print_detail itsty (icnt + 2),
  trace format!"{indent})"
| (expr.app a1 a2) icnt := do
  let indent := list.as_string (list.repeat ' ' icnt), 
  trace format!"{indent}(app",
  print_detail a1 (icnt + 2),
  print_detail a2 (icnt + 2),
  trace format!"{indent})"
| (expr.lam n b e e') icnt := do
  let indent := list.as_string (list.repeat ' ' icnt), 
  trace format!"{indent}(lam {n}",
  print_detail e (icnt + 2),
  print_detail e' (icnt + 2),
  trace format!"{indent})"
| (expr.pi n b e e') icnt := do
  let indent := list.as_string (list.repeat ' ' icnt), 
  trace format!"{indent}(pi {n}",
  print_detail e (icnt + 2),
  print_detail e' (icnt + 2),
  trace format!"{indent})"
| (expr.elet n e1 e2 e3) icnt := do
  let indent := list.as_string (list.repeat ' ' icnt), 
  trace format!"{indent}(elet {n}",
  print_detail e1 (icnt + 2),
  print_detail e2 (icnt + 2),
  print_detail e3 (icnt + 2),
  trace format!"{indent})"
| (expr.macro _ _) _ := fail "Unsupported case"
| (expr.var v) icnt := do
  let indent := list.as_string (list.repeat ' ' icnt), 
  trace format!"{indent}(var {v})"
| (expr.sort lvl) icnt := do
  let indent := list.as_string (list.repeat ' ' icnt), 
  trace format!"{indent}(sort {lvl})"
| (expr.const n levels) icnt := do
  let indent := list.as_string (list.repeat ' ' icnt), 
  trace format!"{indent}(const {n} {levels})"
| (expr.mvar n1 n2 _) icnt := do
  let indent := list.as_string (list.repeat ' ' icnt), 
  trace format!"{indent}(mvar {n1} {n2} _)"

meta def is_inequality (tyname:name):bool :=
  tyname = `has_lt.lt ∨ tyname = `has_le.le ∨
  tyname = `gt ∨ tyname = `ge ∨ tyname = `lt ∨ tyname = `le

-- Utility functions
-- Replaces name with val.
-- If nested_only is tt, it replaces things only inside
-- the expression.
meta def replace (name:expr) (val:expr): bool → expr → expr
| nested_only x@(expr.local_const n m b itsty) :=
  if x = name ∧ ¬ nested_only then val
  else expr.local_const n m b (replace ff itsty)
| nested_only (expr.app e1 e2) :=
  expr.app (replace ff e1) (replace ff e2)
| nested_only (expr.pi n b nty e) :=
  expr.pi n b (replace ff nty) (replace ff e)
| nested_only (expr.lam n b nty e) :=
  expr.lam n b (replace ff nty) (replace ff e)
| nested_only x := x -- for all other cases - just give up! :(
-- Get all bound variables inside an expression.   
meta def get_allvars: expr → tactic (list var)
| e@(expr.local_const _ n _ itsty) := return [e]
| (expr.app f g) := do
  l1 ← get_allvars f,
  l2 ← get_allvars g,
  return (l1.union l2)
| (expr.lam n b nty e2) := do
  l1 ← get_allvars nty,
  l2 ← get_allvars e2,
  return (l1.union (l2.filter (λ i,
      ¬ (n = i.local_uniq_name ∧ nty = i.local_type))))
| (expr.pi n b nty e2) := do
  l1 ← get_allvars nty,
  l2 ← get_allvars e2,
  return (l1.union (l2.filter (λ i,
      ¬ (n = i.local_uniq_name ∧ nty = i.local_type))))
| (expr.elet _ _ _ _) := fail "Unsupported case"
| (expr.macro _ _) := fail "Unsupported case"
| (expr.var _) := return []
| (expr.sort _) := return []
| (expr.const _ _) := return []
| (expr.mvar _ _ _) := return []
-- Remove parameters and return the type name of e.
-- ex) bitvector 8 -> bitvector
meta def get_typename (e:expr): tactic name :=
  match (e.get_app_fn) with
  | expr.const n _ := return n
  | _ := do
    trace "??",
    print_detail e 2,
    fail "cannot get typename"
  end

-- A list of assignments.
@[reducible]
meta def assns := list (var × expr)

namespace assns
  meta def assign (a:assns) (v:var) (val:expr) :=
    (v, val)::a

  meta def get (a:assns) (v:var): option expr :=
    match (list.filter (λ (i:var × expr), i.1 = v) a) with
    | head::tail := some head.2
    | _ := none
    end

  meta def erase (a:assns) (v:var):assns :=
    list.filter (λ itm, itm.1 ≠ v) a
  
  -- Replaces all occurrences of variables in e
  -- with corresponding value if there exists an assignment.
  -- If `nested_only` is tt, it replaces only nested expressions
  -- inside e.
  meta def replace_all (a:assns) (e:expr) (nested_only:bool): expr :=
    list.foldl (λ (s:expr) (y:var × expr),
        -- Replace y.1.1 in s with y.2.
        replace y.1 y.2 nested_only s) e a
end assns


-- Random value generator.
meta def valgen := (assns × std_gen) → tactic (expr × assns × std_gen)

meta structure test_env :=
  (vars:list var) -- Variables
  (goal:expr) -- goal
  (a:assns) -- Assignments to the variables
  (g:std_gen) -- Random value generator
  -- Lazy evaluator of variables.
  (f:var → valgen)

namespace test_env
  -- Creates an empty testing context
  meta def new (vars:list var) (goal:expr) (randgen:std_gen):test_env :=
    test_env.mk vars goal [] randgen
      (λ (x:var) (y:assns × std_gen), do
        trace "Uninitialized variable:",
        print_detail x 2,
        fail "Uninitialized variable")

  -- Adds a new uninitializd variable.
  meta def add_var (tenv:test_env) (v:var):test_env :=
    ⟨tenv.vars ++ [v], -- preserves order
     tenv.goal, tenv.a, tenv.g, tenv.f⟩

  -- Replace v in tenv.vars with v'
  meta def replace_var_at (tenv:test_env) (idx:nat) (newv:var):tactic test_env :=
    do
    v ← tenv.vars.nth idx,
    return ⟨tenv.vars.map (λ x, if x = v then newv else x),
      tenv.goal, tenv.a.map (λ x, if x.1 = v then (newv, x.2) else x),
      tenv.g,
      (λ x, if x = newv then tenv.f v else tenv.f x)⟩

  -- Updates random value generator
  meta def update_gen (tenv:test_env) (newgen:std_gen):test_env :=
    ⟨tenv.vars, tenv.goal, tenv.a, newgen, tenv.f⟩

  -- Updates goal.
  meta def update_goal (tenv:test_env) (newgoal:expr):test_env :=
    ⟨tenv.vars, newgoal, tenv.a, tenv.g, tenv.f⟩

  meta def has_value (tenv:test_env) (v:var):bool :=
    tenv.a.get v ≠ none

  -- Get the assigned value.
  meta def get (tenv:test_env) (v:var):tactic expr :=
    let err:tactic expr := do
      trace format!"test_env.get:Unknown variable",
      trace "finding variable:",
      print_detail v 0,
      trace "each vars:",
      monad.foldl (λ _ (v:var), do
          print_detail v 0) () tenv.vars,
      fail format!"test_env.get:Unknown variable {v}" in
    if tenv.vars.mem v then
      match tenv.a.get v with
      | none := err
      | some n := return n
      end
    else err

  -- Gets the value expression assigned to the variable.
  -- If there's no such value, create a new value and assign it.
  meta def get_or_init (tenv:test_env) (v:var):tactic (expr × test_env) :=
    if tenv.vars.mem v then
      match tenv.a.get v with
      | none := do
        (val, a, g) ← tenv.f v (tenv.a, tenv.g),
        return (val, ⟨tenv.vars, tenv.goal, a.assign v val, g, tenv.f⟩)
      | some n :=
        return (n, tenv)
      end
    else do
      trace format!"test_env.get_or_init:Unknown variable",
      trace "finding variable:",
      print_detail v 0,
      trace "each vars:",
      monad.foldl (λ _ (v:var), do
          print_detail v 0) () tenv.vars,
      fail format!"test_env.get_or_init:Unknown variable {v}"

  -- Evaluate the expression which is assigned to the variable.
  meta def eval (tenv:test_env) (v:var) (retty:Type) [reflected retty]
    :tactic retty :=
    match (tenv.a.get v) with
    | some vexpr := do
      v ← eval_expr retty vexpr,
      return v
    | none := fail "Cannot find assignment to the variable"
    end

  -- Replace all occurrences of variable v in vars and goal
  -- into its assigned value.
  meta def replace_all (tenv:test_env) (v:var): test_env :=
    ⟨tenv.vars.map (λ (i:var),
              if v ≠ i then
                -- variable name contains type as well.
                -- However, 
                (tenv.a.replace_all i tt)
              else i),
            tenv.a.replace_all tenv.goal ff,
            tenv.a, tenv.g, tenv.f⟩

  -- Adds a lazy evalutor for the variable.
  meta def add_evaluator (tenv:test_env) (v:var) (f:valgen)
    :test_env :=
    ⟨tenv.vars, tenv.goal, tenv.a, tenv.g,
      (λ v0, if v0 = v then f else tenv.f v0)⟩

end test_env


-- Pick a random value of given type and assign to it.
-- valgen = (assns × std_gen) → tactic (expr × assns × std_gen)
meta def pick :var → valgen
| v f :=
  let (a, gen) := f in
  do
  tyname ← get_typename v.ty,
  if tyname = `size then
    do
    let (n,gen') := std_next gen,
    let n := n % 5,
    let ne := `(n),
    return (`(size.incr_nat %%ne), a, gen')
  else if tyname = `bitvector then
    do
    -- size of bitvector is already concretized by process_type.
    `(bitvector %%sze) ← pure v.ty,
    sz ← eval_expr size sze,
    let (n,gen') := std_next gen,
    let n' := n % (2^sz.val),
    let n'e := `(n'),
    e ← to_expr ``(bitvector.of_int %%sze %%n'e),
    return (e, a, gen')
  else if tyname = `sbitvec then
    do
    -- size of sbitvec is already concretized by process_type.
    -- Assign sbitvec.var!
    `(sbitvec %%sze) ← pure v.ty,
    sz ← eval_expr size sze,
    let vname := to_string v,
    let vnamee := `(vname),
    e ← to_expr ``(sbitvec.var %%sze %%vnamee),
    return (e, a, gen)
  else if tyname = `bool then
    do
    let (n, gen') := std_next gen,
    let b:bool := n % 2 = 0,
    let be := `(b),
    return (be, a, gen')
  else if tyname = `sbool then
    do
    -- Assign sbool.var!
    let vname := to_string v,
    let vnamee := `(vname),
    be' ← to_expr ``(sbool.var %%vnamee),
    return (be', a, gen)
  else if tyname = `int then
    do
    let (n, gen') := std_next gen,
    let ne := `(((int.of_nat n) - (int.of_nat n) * 2)),
    return (ne, a, gen')
  else if tyname = `nat then
    do
    let (n, gen') := std_next gen,
    let ne := `(n),
    return (ne, a, gen')
  else
    do
    trace v,
    fail "Unknown type!"


-- Checks whether the type can be encoded into SMT.
meta def can_encode_to_smt (tyexpr:expr): tactic bool :=
  if tyexpr.is_arrow then return tt
  else do
    n ← get_typename tyexpr,
    return (n = `eq ∨ n = `or ∨ n = `and ∨
            n = `spec.bv_equiv ∨ n = `spec.b_equiv ∨ n = `true ∨ n = `false ∨
            n = `bitvector ∨ n = `sbitvec ∨
            n = `bool ∨ n = `int) -- no natural number now.

-- Replace all occurrences of variables in e with its value,
-- as well as all other occurences in test_env.
-- If leave_vars is tt, variables are not instantiated unless
-- it is used by functions which cannot be encoded to SMT.
-- For example, if leave_vars = tt, then term `x op y` does not
-- instantiate x and y if it is known that 'op has its corresponding
-- SMT operation.
meta def concretize: test_env → expr → bool → tactic (test_env × expr)
| tenv e leave_vars := do
  if leave_vars ∧ e.is_local_constant then do
    -- Don't initialize it if e is just a variable.
    -- Otherwise it removes opportunity to use 'forall' in SMT.
    return (tenv, e)
  else do
    flag ← can_encode_to_smt e,
    if flag ∧ leave_vars then do
      -- ex: "p = q"
      let args := e.get_app_args,
      let f := e.get_app_fn,
      (tenv, args') ← monad.foldl (λ (x:test_env × list expr) (arg:expr), do
        let tenv := x.1,
        -- Replace all initialized variables with
        -- its corresponding value.
        let arg := tenv.a.replace_all arg ff,
        (tenv, arg') ← concretize tenv arg leave_vars,
        return (tenv, x.2 ++ [arg']))
        (tenv, []) args,
      return (tenv, f.app_of_list args')
    else do
      vars ← get_allvars e,
      res ← monad.foldl (λ (x:test_env × expr) v, do
          --print_detail v 2,
          let (tenv, e) := x,
          (val, tenv) ← tenv.get_or_init v, -- Give random value to v
          -- Replace all occurrences of v with its value
          let tenv := tenv.replace_all v,
          let e := replace v val ff e,
          return (tenv, e))
        (tenv, e) vars,
      return res


meta mutual def process_eq, process_ineq,
    process_implies, process_and,
    process_or, process_bv_equiv_opt,
    process_bv_equiv, process_b_equiv_opt,
    process_b_equiv, process_type

-- Processes `P = Q`
-- Currently equality does nothing special.
with process_eq: test_env → expr → tactic (test_env × option expr)
| tenv pty := do
  (tenv, e) ← concretize tenv pty tt,
  return (tenv, some e)

-- Processes 'P > Q', 'P ≤ Q', ...
with process_ineq: test_env → expr → tactic (test_env × option expr)
| tenv pty := do
  (tenv, e) ← concretize tenv pty tt,
  b ← try_core (do
      pre_cast ← to_expr ``(to_bool %%e),
      b ← eval_expr bool pre_cast,
      return b),
  match b with
  | some b :=
    return (tenv, if b then some `(true) else some `(false))
  | none := fail "Converting inequality into SMT is not supported ; should be eagerly evaluated"
  end

-- Processes `P → Q`
with process_implies: test_env → expr → tactic (test_env × option expr)
| tenv pty@(expr.pi n bi pre post) :=
  do
  (tenv, pre) ← concretize tenv pre tt, -- Let's concretize precondition first.
  -- Can we evaluate this precondition in Lean?
  -- (e.g. is all local variables in precondition initialized?)
  pre_b ← try_core (do
      pre_cast ← to_expr ``(to_bool %%pre),
      b ← eval_expr bool pre_cast,
      return b),
  match pre_b with
  | some ff := -- Precondition evaluates to false!
    -- We can just remove this implies term, if allowed.
    return (tenv, none)
  | some tt := -- Precondition is true, equivalent to postcondition only.
    process_type tenv post 
  | none := -- Let's process postcondition now.
    do
    (tenv, post) ← concretize tenv post tt,
    return (tenv, expr.pi n bi pre post)
  end
| _ _ := fail "Invalid argument"

-- Processes `P ∧ Q`
with process_and: test_env → expr → tactic (test_env × option expr)
| tenv pty :=
  do
  `(and %%e1 %%e2) ← pure pty,
  (tenv, oe1) ← process_type tenv e1,
  (tenv, oe2) ← process_type tenv e2,
  match oe1, oe2 with
  | none, none := return (tenv, none)
  | some e1, none := return (tenv, some e1)
  | none, some e2 := return (tenv, some e2)
  | some e1, some e2 := do
    e ← to_expr ``(and %%e1 %%e2),
    return (tenv, e)
  end

-- Processes `P ∨ Q`
with process_or: test_env → expr → tactic (test_env × option expr)
| tenv pty :=
  do
  `(or %%e1 %%e2) ← pure pty,
  (tenv, e1) ← concretize tenv e1 tt,
  (tenv, e2) ← concretize tenv e2 tt,
  e ← to_expr ``(or %%e1 %%e2),
  return (tenv, some e)

-- Processes `bv_equiv s b`, assign s = (sbitvec.of_bv b) if possible
with process_bv_equiv_opt: test_env → expr → tactic (test_env × option expr)
| tenv pty :=
  do
  `(spec.bv_equiv %%s %%b) ← pure pty,
  if s.is_local_constant then do
    -- s is just a simple variable.
    -- Let's replace s with (sbitvec.of_bv b).
    -- Then, this bv_equiv can be removed.
    b' ← to_expr ``(sbitvec.of_bv %%b),
    (tenv, b') ← concretize tenv b' tt,
    let f:valgen := (λl, return (b', l.1, l.2)),
    let tenv := tenv.add_evaluator s f,
    return (tenv, none)
  else do
    -- Eagerly assign all variables in s.
    (tenv, s) ← concretize tenv s tt,
    (tenv, b) ← concretize tenv b tt,
    e ← to_expr ``(spec.bv_equiv %%s %%b),
    return (tenv, some e)

-- Processes `bv_equiv s b`
with process_bv_equiv: test_env → expr → tactic (test_env × option expr)
| tenv pty :=
  do
  `(spec.bv_equiv %%s %%b) ← pure pty,
  (tenv, s) ← concretize tenv s tt,
  (tenv, b) ← concretize tenv b tt,
  e ← to_expr ``(spec.bv_equiv %%s %%b),
  return (tenv, some e)

-- Processes `b_equiv s b`, assign s = (sbool.of_bool b) if possible
with process_b_equiv_opt: test_env → expr → tactic (test_env × option expr)
| tenv pty :=
  do
  `(b_equiv %%s %%b) ← pure pty,
  if s.is_local_constant then do
    -- s is just a simple variable.
    -- Let's replace s with (sbool.of_bool b).
    -- Then, this b_equiv can be removed.
    sty ← infer_type s,
    b' ← to_expr ``(sbool.of_bool %%b),
    (tenv, b') ← concretize tenv b' tt,
    let f:valgen := (λl, return (b', l.1, l.2)),
    let tenv := tenv.add_evaluator s f,
    return (tenv, none)
  else do
    -- Eagerly assign all variables in s.
    (tenv, s) ← concretize tenv s tt,
    (tenv, b) ← concretize tenv b tt,
    e ← to_expr ``(b_equiv %%s %%b),
    return (tenv, some e)

-- Processes `bv_equiv s b`
with process_b_equiv: test_env → expr → tactic (test_env × option expr)
| tenv pty :=
  do
  `(spec.b_equiv %%s %%b) ← pure pty,
  (tenv, s) ← concretize tenv s tt,
  (tenv, b) ← concretize tenv b tt,
  e ← to_expr ``(spec.b_equiv %%s %%b),
  return (tenv, some e)


-- Returns new test environmen × optimized expression.
-- (ex: bitvector sz -> bitvector 8)
-- If the expression can be totally removed, it returns none.
-- Otherwise, it returns the updated expression.
with process_type: test_env → expr → tactic (test_env × option expr)
| tenv pty :=
  do
  is_prop ← is_prop pty,
  match is_prop with
  | tt := do -- it is Prop!
    (tenv, oe) ← (
      if pty.is_arrow then
        process_implies tenv pty
      else do
        tyname ← get_typename pty,
        if tyname = `eq then process_eq tenv pty
        else if is_inequality tyname then
            process_ineq tenv pty
        else if tyname = `or then process_or tenv pty
        else if tyname = `and then process_and tenv pty
        else if tyname = `spec.bv_equiv then process_bv_equiv tenv pty
        else if tyname = `spec.b_equiv then process_b_equiv tenv pty
        else fail "."),
    return (tenv, oe)
  | ff := do -- it is not Prop.
    -- Eagerly assign parameters of the type.
    -- eg) bitvector sz
    -- Here, sz should be initialized immediately.
    (tenv, pty) ← concretize tenv pty ff,
    return (tenv, some pty)
  end

-- Evaluates e(ex: `1+1` -> 2), and returns a string that encodes e
-- so it can be used in SMT code.
meta def eval_and_tosmtstr (e:expr):tactic string :=
  do
  ty ← infer_type e,
  tn ← get_typename ty,
  ostr ← try_core (
    if tn = `bitvector then do
      e ← to_expr ``(to_string (sbitvec.of_bv %%e)),
      str ← eval_expr string e,
      return str
    else if tn = `sbitvec then do
      e ← to_expr ``(to_string (%%e)),
      str ← eval_expr string e,
      return str
    else if tn = `int then do
      i ← eval_expr int e,
      return (to_string i)
    else if tn = `bool then do
      if e = `(bool.tt) then
        return "true"
      else if e = `(bool.ff) then
        return "false"
      else do
        b ← eval_expr bool e,
        return (if b then "true" else "false")
    else fail ""),
  match ostr with
  | none := do
    -- I wish this will work in general..
    fmt ← tactic_format_expr e,
    return (to_string fmt)
  | some s := return s
  end

-- smt2.term does not have has_to_pexpr, so expr_to_string / prop_to_smt
-- is currently returning string instead of smt2.term.
meta mutual def expr_to_smt, prop_to_smt
with expr_to_smt: test_env → expr → tactic string
| tenv e :=
  do
  is_prop ← is_prop e,
  match is_prop with
  | tt := prop_to_smt tenv e
  | ff := do
    str ← eval_and_tosmtstr e,
    return str
  end

with prop_to_smt: test_env → expr → tactic string
| tenv ty :=
  do
  e ← (
    if ty.is_arrow then do
      let p := ty.binding_domain,
      let q := ty.binding_body,
      sp ← prop_to_smt tenv p,
      sq ← prop_to_smt tenv q,
      --e ← to_expr ``(smt2.builder.implies %%sp %%sq),
      return $ to_string (format!"(=> {sp} {sq})")
    else do
      tyname ← get_typename ty,
      if tyname = `eq then do
      `(eq %%p %%q) ← pure ty,
      sp ← expr_to_smt tenv p,
      sq ← expr_to_smt tenv q,
      return $ to_string (format!"(= {sp} {sq})")
    else if tyname = `or then do
      `(or %%p %%q) ← pure ty,
      sp ← prop_to_smt tenv p,
      sq ← prop_to_smt tenv q,
      return $ to_string (format!"(or {sp} {sq})")
    else if tyname = `and then do
      `(and %%p %%q) ← pure ty,
      sp ← prop_to_smt tenv p,
      sq ← prop_to_smt tenv q,
      return $ to_string (format!"(and {sp} {sq})")
    else if tyname = `spec.bv_equiv then do
      `(@spec.bv_equiv %%sz %%s %%b) ← pure ty,
      se ← to_expr ``(to_string (%%s)),
      sstr ← eval_expr string se,
      be ← to_expr ``(to_string (sbitvec.of_bv %%b)),
      bstr ← eval_expr string be,
      return $ to_string (format!"(= {sstr} {bstr})")
    else if tyname = `spec.b_equiv then do
      `(b_equiv %%s %%b) ← pure ty,
      se ← to_expr ``(to_string (%%s)),
      sstr ← eval_expr string se,
      bse ← to_expr ``(to_string (sbool.of_bool %%b)),
      bstr ← eval_expr string bse,
      return $ to_string (format!"(= {sstr} {bstr})")
    else if tyname = `true then do
      return "true"
    else if tyname = `false then do
      return "false"
    else
      do
      trace ty,
      fail "Unknown goal type"),
  return e


-- Creates a variable which can be used for forall quantifier.
meta def var_to_smtvar (tenv:test_env) (v:var): tactic (option (string × smt2.sort)) :=
  do
  tyname ← get_typename v.ty,
  if tyname = `size then
    -- size should be initialized in Lean.
    if tenv.has_value v then return none
    else fail "size should be initialized in Lean."
  else if tyname = `bitvector then
    if tenv.has_value v then return none
    else do
      -- sz should be already concretized.
      `(bitvector %%sz) ← pure v.ty,
      sz ← eval_expr size sz,
      return (to_string v,
              smt2.sort.apply "_" ["BitVec", to_string sz])
  else if tyname = `sbitvec then
    -- a BitVec variable creator.
    let newvar := λ (sze:expr) (vname:string), do
        -- sz should be already concretized.
        sz ← eval_expr size sze,
        return (some (vname,
                smt2.sort.apply "_" ["BitVec", to_string sz]))
      in
    if tenv.has_value v then do
      val ← tenv.get v,
      -- If sbitvec.var is assigned, it can be forall quantified.
      o ← try_core (do
        `(sbitvec.var %%sze %%varnamee) ← pure val,
        varname ← eval_expr string varnamee,
        return (sze, varname)
        ),
      match o with
      | none := return none -- it's not variable.
      | some (sz, vname) := newvar sz vname
      end
    else do
      `(sbitvec %%sz) ← pure v.ty,
      newvar sz (to_string v)
  else if tyname = `bool then
    if tenv.has_value v then return none
    else return (to_string v,
                 smt2.sort.id "Bool")
  else if tyname = `sbool then
    if tenv.has_value v then do
      val ← tenv.get v,
      -- If sbitvec.var is assigned, it can be forall quantified.
      o ← try_core (do
        `(sbool.var %%varnamee) ← pure val,
        varname ← eval_expr string varnamee,
        return varname
        ),
      match o with
      | none := return none -- it's not variable.
      | some vname :=
        return (some (vname, smt2.sort.id "Bool"))
      end
    else do
        return (some (to_string v, smt2.sort.id "Bool"))
  else if tyname = `int then
    if tenv.has_value v then return none
    else return (to_string v,
                smt2.sort.id "Int")
  else
    do
    trace v,
    fail "Unknown type!"

meta def update_smt (tenv:test_env) (orgsmt: string) (v:var): tactic string :=
  do
  is_prop ← is_prop v.ty,
  match is_prop with
  | tt := do
    t ← prop_to_smt tenv v.ty,
    return $ to_string (format!"(=> {t} {orgsmt})")
  | ff := do
    ovar ← var_to_smtvar tenv v,
    match ovar with
    | none := -- Isn't needed to create forall.
      return orgsmt
    | some (vname, sort) :=
      -- Make (forall x, P).
      return $ to_string (format!"(forall (({vname} {sort})) {orgsmt})")
    end
  end

meta def build_smt (tenv:test_env): tactic string :=
  do
  -- First, synthesize goal.
  smt ← prop_to_smt tenv tenv.goal,
  smt ← monad.foldl (update_smt tenv) smt (tenv.vars.reverse),
  return $ to_string (format!"(assert {smt})")

meta def run_smt (smtcode:string) : io smt2.response :=
  do
  z3i ← z3_instance.start,
  smtres ← z3_instance.raw z3i (smtcode ++ " (check-sat)"),
  pure (parse_smt2_result smtres)


meta def visit_each_param :test_env → nat → tactic test_env
| tenv n :=
  if tenv.vars.length ≤ n then return tenv
  else do
    v ← tenv.vars.nth n,
    (tenv, oe) ← process_type tenv v.ty,
    match oe with
    | none :=
      -- This parameter is optimized out.
      -- Remove the param from testing environment later.
      visit_each_param tenv (n+1)
    | some e' := do
      let newv := v.setty e',
      is_prop ← is_prop v.ty,
      tenv ← tenv.replace_var_at n newv,
      visit_each_param (if ¬ is_prop then
          tenv.add_evaluator newv (pick newv)
          else tenv) (n+1)
    end

meta def test_can_be_omitted (tenv:test_env): bool :=
  tenv.vars.any (λ v, v.ty = `(false))

inductive test_result:Type
| success | fail | unknown | error : string → test_result | omitted
instance : decidable_eq test_result :=
by tactic.mk_dec_eq_instance
instance : has_to_string test_result :=
⟨λ r, match r with
  | test_result.success := "success"
  | test_result.fail := "fail"
  | test_result.unknown := "unknown"
  | test_result.error s := "error(" ++ s ++ ")"
  | test_result.omitted := "omitted"
  end ⟩

-- Main function.
meta def test (spec : expr) (gen:std_gen)
    :tactic (string × test_result × std_gen) :=
  do
  -- 1. Infer the type of specificaton
  t ← infer_type spec,
  -- 2. Segregate arguments from the type, and
  --   infer types of the input arguments.
  --   ex) get a, b from Π (a:nat) (b:nat), P a b
  (params, goal) ← mk_local_pis t,
  -- 3. Create the test environment.
  let tenv := test_env.new params goal gen,
  -- 4. Process each parameter.
  tenv ← visit_each_param tenv 0,
  -- 5. Process goal.
  (tenv, some newgoal) ← process_type tenv tenv.goal,
  let tenv := tenv.update_goal newgoal,
  -- 6. If a test can be omitted, stop here.
  if test_can_be_omitted tenv then
    return ("", test_result.omitted, tenv.g)
  else do
    -- 7. Synthesize SMT code.
    smtcode ← build_smt tenv,
    let smtcode_expr := `(smtcode),
    tgt ← to_expr ``(run_smt %%smtcode_expr),
    tgt ← eval_expr (io smt2.response) tgt,
    res ← unsafe_run_io tgt,
    return (smtcode, match res with
      | smt2.response.sat := test_result.success
      | smt2.response.unsat := test_result.fail
      | smt2.response.unknown := test_result.unknown
      | smt2.response.other s := test_result.error s
      end, tenv.g)

end proptest

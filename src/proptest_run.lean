-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import system.io
import .smtexpr
import .smtcompile
import .spec.spec
import .proptest
import .spec.lemmas

open tactic
open spec

axiom inteq: (3:int) = 3
axiom inteq2: (3:int) = 1+2
axiom forall1 : ∀ (x:int), x = x
axiom forall2_unsat : ∀ (x y:int), x = y
axiom forall3 : ∀ (x:int), x + 2 = x + 1 + 1
axiom forall4 : ∀ (x y:int), x + 2 = x + 1 + 1
axiom intlt: (3:int) < 4

def stat := list (proptest.test_result × nat)

namespace stat
  def new:stat := []

  def incr (s:stat) (r:proptest.test_result) :=
    if s.any (λ l, l.1 = r) then
      s.map (λ c, if c.1 = r then (c.1, c.2 + 1)  else c)
    else
      (r, 1)::s

  def to_string (s:stat) :=
    s.foldl (λ s itm,
      s ++
      (to_string itm.1) ++ " : " ++ (to_string itm.2) ++ "\n"
      ) ""
end stat

meta def test_n_loop (e:expr) : nat → std_gen → stat → tactic (stat × std_gen)
| n g s :=
  if n = 0 then return (s, g)
  else do
    if n % 1000 = 0 then do
      trace n
    else skip,
    (smtcode, r, g) ← proptest.test e g,
    let s := s.incr r,
    match r with
    | proptest.test_result.error errmsg := do
      trace "SMT error!",
      trace errmsg,
      fail "SMT error!"
    | proptest.test_result.fail := do
      trace "Counter example:",
      trace smtcode,
      test_n_loop (n - 1) g s
    | _ :=
      test_n_loop (n - 1) g s
    end

meta def test_n (e:expr) (g:std_gen) (n:nat) : tactic std_gen :=
  do
  trace format!"--------- test_n: total {n} times",
  trace e,
  ety ← infer_type e,
  trace ety,
  (s, g) ← test_n_loop e n g stat.new,
  trace (s.to_string),
  return g


meta def arith: list expr :=
  [ `(inteq),
    `(inteq2),
    `(forall1),
    `(forall2_unsat),
    `(forall3),
    `(forall4),
    `(intlt) ]

meta def bv_equiv_cons: list expr :=
  [ `(@spec.bv_equiv.add),
    `(@spec.bv_equiv.sub),
    `(@spec.bv_equiv.mul),
    `(@spec.bv_equiv.and),
    `(@spec.bv_equiv.or),
    `(@spec.bv_equiv.xor),
    `(@spec.bv_equiv.shl),
    `(@spec.bv_equiv.lshr),
    `(@spec.bv_equiv.ashr),
    `(@spec.bv_equiv.udiv),
    `(@spec.bv_equiv.urem),
    `(@spec.bv_equiv.sdiv),
    `(@spec.bv_equiv.srem),
    `(@spec.bv_equiv.ite),
    `(@spec.bv_equiv.of_bool),
    `(@spec.bv_equiv.trunc),
    `(@spec.bv_equiv.zext),
    `(@spec.bv_equiv.sext) ]

meta def b_equiv_cons: list expr :=
  [ `(@spec.b_equiv.tt),
    `(@spec.b_equiv.ff),
    `(@spec.b_equiv.and1),
    -- ∀ (s1 s2:sbool) (b1 b2:bool),
    --     b_equiv s1 b1 → (b1 = tt → b_equiv s2 b2) → b_equiv (s1.and s2) (band b1 b2)
    -- =>
    -- (assume that we randomly assigned b1 := tt, b2 := ff)
    -- ∀ (s1 s2:sbool),
    --      b_equiv s1 tt → (tt = tt → b_equiv s2 ff) → b_equiv (s1.and s2) (ff)
    -- .. then this is turned into SMT formula & checked by Z3
    `(@spec.b_equiv.and2),
    `(@spec.b_equiv.or1),
    `(@spec.b_equiv.or2),
    `(@spec.b_equiv.xor),
    `(@spec.b_equiv.not),
    `(@spec.b_equiv.ite),
    `(@spec.b_equiv.eq),
    `(@spec.b_equiv.ne),
    `(@spec.b_equiv.ult),
    `(@spec.b_equiv.ule),
    `(@spec.b_equiv.slt),
    `(@spec.b_equiv.sle)]

meta def overflow_chks: list expr :=
  [ `(@spec.add_overflow_chk),
    `(@spec.sub_overflow_chk),
    `(@spec.mul_overflow_chk),
    `(@spec.shl_overflow_chk) ]

open io

meta def main:io unit :=
  let failmsg:io unit := do
      print_ln "proptest_run.lean <testset> <all/i> <itrcnt>",
      print_ln "<testset>:",
      print_ln format!"\tarith: 0 ~ 6",
      print_ln format!"\tbv_equiv: 0 ~ {bv_equiv_cons.length}",
      print_ln format!"\tb_equiv: 0 ~ {b_equiv_cons.length}",
      print_ln format!"\toverflow_chk: 0 ~ {overflow_chks.length}",
      return () in do
  args ← io.cmdline_args,
  match args with
  | testset::id::cnt::_ :=
    let exprs := match testset with
        | "arith" := arith | "bv_equiv" := bv_equiv_cons
        | "b_equiv" := b_equiv_cons | "overflow_chk" := overflow_chks
        | _ := [] end in
    if exprs.length = 0 then
      failmsg
    else
      let n := cnt.to_nat in
      let gen := mk_std_gen in do
      exprs ← (if id = "all" then return exprs else
        match exprs.nth (id.to_nat) with
        | some e := return [e]
        | none := do failmsg, io.fail ""
        end),
      gen' ← monad.foldl (λ gen e,
          run_tactic (test_n e gen n)) gen exprs,
      return ()
  | _ := failmsg
  end

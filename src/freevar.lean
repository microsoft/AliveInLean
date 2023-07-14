-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import .lang
import .irsem
import .irsem_exec
import .irsem_smt
import smt2.syntax
import smt2.builder

namespace freevar

open irsem
open io

def update (lhses:list string) (t:ty) (op:operand) (freevs:list (string × ty)) : list (string × ty) :=
  match op with
  | operand.const _ := freevs
  | operand.reg (reg.r lname) :=
    if bor (list.mem lname lhses) (list.mem (lname, t) freevs)
    then freevs else (lname, t)::freevs
  end

-- Returns the list of free variables from the program
def get (typed_prog:program): list (string × ty) :=
  let res:(list string × list (string × ty)) := typed_prog.insts.foldl
    (λ res (inst:instruction),
    let update := update res.1 in
    match inst with
    | instruction.binop retty (reg.r lhsname) _ _ op1 op2 :=
        (lhsname::(res.1),
          update retty op1 (update retty op2 res.2))
    | instruction.unaryop (reg.r lhsname) _ fromty op toty :=
        (lhsname::(res.1), update fromty op res.2)
    | instruction.selectop (reg.r lhsname) condty condop opty op1 op2 :=
        (lhsname::(res.1),
          update condty condop
            (update opty op1
            (update opty op2 res.2)))
    | instruction.icmpop opty (reg.r lhsname) _ op1 op2 :=
        (lhsname::(res.1),
          update opty op1 (update opty op2 res.2))
    end) ([], []) in
  res.2


def get_sz_from_ty (t:ty): size :=
  let isz := (match t with | ty.int isz := isz | _ := 16 end) in
  if H:isz > 0 then subtype.mk isz H else ⟨1, dec_trivial⟩

def get_rand_bv (sz:size) (sg:std_gen): irsem_exec.intty sz × std_gen :=
  let (n, sg) := std_next sg in
  (⟨n % 2^sz.val, by apply bitvector.bv_mod_lt⟩, sg)

def get_rand_bool (sg:std_gen): bool × std_gen :=
  let (n, sg) := std_next sg in
  (if n = 0 then ff else tt, sg)

def get_free_sbitvec_name (name:string) := "v_" ++ name
def get_free_sbitvec (name:string) (sz:size): sbitvec sz :=
  sbitvec.var sz (get_free_sbitvec_name name)

def get_free_sbool_name (name:string) := "b_" ++ name
def get_free_sbool (name:string): sbool :=
  sbool.var (get_free_sbool_name name)

set_option eqn_compiler.zeta true
def create_init_var_exec (name:string) (t:ty) (s:irstate irsem_exec × std_gen)
  : (irstate irsem_exec × std_gen) :=
  let sz := get_sz_from_ty t in
  let (bv, sg) := get_rand_bv sz s.2 in
  let (b, sg) := get_rand_bool sg in
  (irstate.updatereg irsem_exec s.1 name
      (irsem.valty.ival sz bv b), sg)

-- Creates a random initial state (of exec. sem) from given free variables
def create_init_state_exec (freevars:list (string × ty)) (sg:std_gen)
  : (irstate irsem_exec × std_gen) :=
  list.foldr (λ (n:string × ty) st, create_init_var_exec n.1 n.2 st)
    (irstate.empty irsem_exec, sg)
    freevars


def create_init_var_smt (name:string) (t:ty) (s:irstate irsem_smt)
  : irstate irsem_smt :=
  let sz := get_sz_from_ty t in
  let bv := get_free_sbitvec name sz in
  let p :=  get_free_sbool name in
  irstate.updatereg irsem_smt s name (irsem.valty.ival sz bv p)

-- Creates an initial state (of smt. sem) from given free variables
def create_init_state_smt (freevars:list (string × ty)): irstate irsem_smt :=
  list.foldr (λ (n:string × ty) st, create_init_var_smt n.1 n.2 st)
    (irstate.empty irsem_smt)
    freevars


-- env η is a mapping from SMT variables to their concrete values.
-- It has two fields: one (bv) for bit-vector SMT variables, and another (b) for
-- boolean SMT variables.
structure env :=
  (bv:string → option int)
  (b:string → option bool)

namespace env
  -- An empty environment
  def empty : env := { bv := (λ n, none), b := λ n, none }

  -- Two functions for adding (name |-> v) to env.
  def add_bv (e:env) (name:string) (v:ℤ):env :=
    {bv := (λ n, if n = name then some v else e.bv n), b := e.b}

  def add_b (e:env) (name:string) (b:bool):env :=
    {bv := e.bv, b := (λ n, if n = name then some b else e.b n)}

  -- Given an SMT formula, replace all free variables with the concrete
  -- value assignments of the environment η. 
  @[simp]
  mutual def replace_sbv, replace_sb
  with replace_sbv: Π (η:env) {sz:size}, sbitvec sz → sbitvec sz
  | η sz x@(sbitvec.var _ name) :=
    match (η.bv name) with
    | some n := sbitvec.of_int sz n
    | none := x
    end
  | η sz (sbitvec.add x y) :=
    sbitvec.add (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.sub x y) :=
    sbitvec.sub (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.mul x y) :=
    sbitvec.mul (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.udiv x y) :=
    sbitvec.udiv (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.urem x y) :=
    sbitvec.urem (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.sdiv x y) :=
    sbitvec.sdiv (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.srem x y) :=
    sbitvec.srem (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.and x y) :=
    sbitvec.and (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.or x y) :=
    sbitvec.or (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.xor x y) :=
    sbitvec.xor (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.shl x y) :=
    sbitvec.shl (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.lshr x y) :=
    sbitvec.lshr (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.ashr x y) :=
    sbitvec.ashr (replace_sbv η x) (replace_sbv η y)
  | η sz (sbitvec.zext sz' y) :=
    sbitvec.zext sz' (replace_sbv η y)
  | η sz (sbitvec.sext sz' y) :=
    sbitvec.sext sz' (replace_sbv η y)
  | η sz (sbitvec.trunc sz' y) :=
    sbitvec.trunc sz' (replace_sbv η y)
  | η sz (sbitvec.extract hb lb H y) :=
    sbitvec.extract hb lb H (replace_sbv η y)
  | η sz (sbitvec.ite c x y) :=
    -- These conditions are necessary to guarantee that recursive functions
    -- replace_sbv, replace_sb are terminating. This is done by defining some
    -- measurement that is strictly decreasing after each recursive call.
    have 2 < (1 + (1 + (1 + (1 + (sbitvec.sizeof sz y + sbitvec.sizeof sz x))))),
      by repeat { rw nat.one_add }; exact dec_trivial,
    have 2 < (1 + (1 + (1 + (1 + (sbitvec.sizeof sz x + sbitvec.sizeof sz y))))),
      by repeat { rw nat.one_add }; exact dec_trivial,
    sbitvec.ite (replace_sb η c) (replace_sbv η x) (replace_sbv η y)
  | η sz c := c

  with replace_sb: Π (η:env) , sbool → sbool
  | η x@(sbool.var name) :=
    match (η.b name) with
    | some b := sbool.of_bool b
    | none := x
    end
  | η (sbool.and x y) :=
    sbool.and (replace_sb η x) (replace_sb η y)
  | η (sbool.or x y) :=
    sbool.or (replace_sb η x) (replace_sb η y)
  | η (sbool.xor x y) :=
    sbool.xor (replace_sb η x) (replace_sb η y)
  | η (sbool.eqb x y) :=
    sbool.eqb (replace_sb η x) (replace_sb η y)
  | η (sbool.neb x y) :=
    sbool.neb (replace_sb η x) (replace_sb η y)
  | η (sbool.ite c x y) :=
    sbool.ite (replace_sb η c) (replace_sb η x) (replace_sb η y)
  | η (sbool.not y) := sbool.not (replace_sb η y)
  | η (@sbool.eqbv sz x y) :=
    have 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    sbool.eqbv (replace_sbv η x) (replace_sbv η y)
  | η (@sbool.nebv sz x y) :=
    have 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    sbool.nebv (replace_sbv η x) (replace_sbv η y)
  | η (@sbool.sle sz x y) :=
    have 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    sbool.sle (replace_sbv η x) (replace_sbv η y)
  | η (@sbool.slt sz x y) :=
    have 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    sbool.slt (replace_sbv η x) (replace_sbv η y)
  | η (@sbool.ule sz x y) :=
    have 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    sbool.ule (replace_sbv η x) (replace_sbv η y)
  | η (@sbool.ult sz x y) :=
    have 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    sbool.ult (replace_sbv η x) (replace_sbv η y)
  | η x := x

  @[simp, reducible]
  def replace_valty (η:env) (v:irsem.valty irsem_smt) :=
    match v with
    | irsem.valty.ival sz i p :=
      @irsem.valty.ival irsem_smt sz (η.replace_sbv i) (η.replace_sb p)
    end

  def replace (η:env) (ss:irstate irsem_smt): irstate irsem_smt :=
    irstate.apply_to_values irsem_smt
        (irstate.setub irsem_smt ss (η.replace_sb (irstate.getub irsem_smt ss)))
      η.replace_valty

  notation η `⟦` s `⟧` := freevar.env.replace η s
  notation η `⟦` v `⟧` := freevar.env.replace_valty η v
  notation η `⟦` sbv `⟧` := freevar.env.replace_sbv η sbv
  notation η `⟦` sb `⟧` := freevar.env.replace_sb η sb
  instance env_has_mem: has_mem string freevar.env :=
  ⟨λ s η, η.b s ≠ none ∨ η.bv s ≠ none⟩
  instance has_mem_decidable (η:freevar.env) (n:string)
  : decidable (n ∈ η) := by apply_instance

end env


-- Creates smt declaration of free variables
def create_smt_declares (freevars:list (string × ty)): smt2.builder unit :=
    monad.foldl (λ (_:unit) (n:string × ty), do
        -- A variable representing concrete value
        smt2.builder.declare_fun (get_free_sbitvec_name n.1) [] (match n.2 with
          | ty.int isz := smt2.sort.apply "_" ["BitVec", to_string isz]
          | _ := smt2.sort.apply "_" ["BitVec", "16"]
          end),
        -- A variable representing poison value
        smt2.builder.declare_fun (get_free_sbool_name n.1) [] "Bool"
        ) () freevars

end freevar

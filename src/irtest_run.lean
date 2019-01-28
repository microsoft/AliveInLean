-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import system.io
import system.random
import .lang
import .lang_tostr
import .irsem
import .irsem_exec
import .freevar

-- Randomly picks an element from a list
def pick {α:Type} (l:list α) (g:std_gen)
    (HPOS:0 < l.length): (α × std_gen) :=
  let (n, g') := std_next g in
  let i := n % l.length in
  (l.nth_le i (by apply nat.mod_lt; apply HPOS), g')

-- Randomly picks a constant
def any_const (t:ty) (g:std_gen): nat × std_gen :=
  let (n, g) := std_next g in
  let const := match t with
    | ty.int isz := n % (2 ^ isz)
    | _ := sorry
    end in
  (const, g)

-- A few utility functions
def powerset {α: Type} : list α → list (list α)
| [h] := [[],[h]]
| (h::t) := (powerset t) ++ (powerset t).map(λ e, h::e)
| [] := []

def is_even (n:nat): bool :=
  n % 2 = 0

-- Opcodes, flags
def bops: list bopcode :=
  [bopcode.add, bopcode.sub, bopcode.mul,
   bopcode.udiv, bopcode.urem, bopcode.sdiv, bopcode.srem,
   bopcode.and, bopcode.or,  bopcode.xor,
   bopcode.shl, bopcode.lshr, bopcode.ashr]

def icmpconds: list icmpcond :=
  [ icmpcond.eq, icmpcond.ne, icmpcond.ugt, icmpcond.uge,
    icmpcond.ult, icmpcond.ule, icmpcond.sgt, icmpcond.sge,
    icmpcond.slt, icmpcond.sle ]

def uops: list uopcode :=
  [ uopcode.sext, uopcode.zext, uopcode.trunc ]

-- Possible integer type sizes.
@[simp]
def ISZ_LIST := [1, 4, 8, 16, 32, 64]

-- The number of instructions in a program
def NUM_INSTS := 5

-- Conversion from a program to a full LLVM IR program
def ir_header := "
define i32 @main() {
entry:
"
def ir_middle := "
  %call1 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i64 0, i64 0), i64 %call)
  ret i32 0
}

declare i32 @printf(i8* nocapture readonly, ...)

@.str = private unnamed_addr constant [4 x i8] c\"%lu\\00\", align 1
"

-- This function is used to resolve type class instance resolution
-- ('unable to synthesize type class instance for n = 64')
def is_64 (n:nat):bool := n = 64

def to_llvmir (p:program) (st:irsem.irstate irsem_exec)
  (freevars:list (string × ty)) (resty:ty): string :=
  let val_as_str (vname:string): string :=
    match st.getreg irsem_exec vname with
        | none := sorry -- should exist
        | some (irsem.valty.ival sz b p) := to_string b.1
        end
    in
  let args_caller:string := freevars.foldl (λ prev (var: string × ty),
      (if prev.length = 0 then "" else prev ++ ", ")
        ++ (to_string var.2) ++ " "
        ++ (val_as_str var.1))
      "" in
  let args_callee:string := freevars.foldl (λ prev (var: string × ty),
      (if prev.length = 0 then "" else prev ++ ", ")
        ++ (to_string var.2) ++ " "
        ++ (to_string var.1))
      "" in
  let retinst:string :=
    match resty with
    | (ty.int isz) :=
      if is_64 isz then "ret i64 %res"
      else "%res.cast = zext " ++ (to_string resty) ++ " %res to i64\n" ++
            "ret i64 %res.cast"
    | _ := sorry
    end in
  ir_header
    ++ "  %call = tail call i64 @f(" ++ args_caller ++ ")"
    ++ ir_middle
    ++ "define i64 @f(" ++ args_callee ++ ") {\n"
    ++ (to_string p)
    ++ retinst ++ "\n}\n"

-- state monad of free variables
structure vars_record :=
  (freevars: list (string × ty))
  (fvnum: int) -- fresh variable id
@[reducible]
def vars_state := state vars_record
def vars_record_empty: vars_record := ⟨[], 0⟩

-- Creates a new free variable.
def fv_new (t:ty): vars_state string :=
do r ← get,
  let name := "%var" ++ (to_string r.2),
  put ⟨(name, t)::r.1, 1 + r.2⟩,
  return name

def fv_remove (name:string): vars_state unit :=
do r ← get,
  put ⟨r.1.filter (λ s, s.1 ≠ name), r.2⟩,
  return ()

-- Creates a random type.
def ty_new (g:std_gen): (ty × std_gen) :=
  let (n, g) := pick ISZ_LIST g (by simp; repeat {constructor}) in
  (ty.int n, g)

-- The likelihood of creating a fresh variable
-- is FRESHVAR_FACTOR times bigger than choosing an existing
-- variable.
def FRESHVAR_FACTOR := 3

-- Chooses an integer-typed variable or create a new one.
-- returns (type of the variable, variable name, is-a-fresh-var, std_gen)
def choose_or_newvar (wantedty: option ty) (g:std_gen)
: vars_state (string × ty × bool × std_gen) :=
  -- type generator
  let tygen: std_gen → (ty × std_gen) := λ (g:std_gen),
    match wantedty with | none := ty_new g | some t := (t, g) end in
do
  r ← get,
  let vars := r.1,
  -- Filter vars with wantedty
  let vars := match wantedty with
    | none := vars | some t := vars.filter (λ x, x.2 = t) end in
  if HPOS:(0 < vars.length) then
    let (n, g) := std_next g in
    let n := n % ((1 + FRESHVAR_FACTOR) * vars.length) in
    if HLT:(n < vars.length) then
      let (name, t) := vars.nth_le n HLT in
      return (name, t, ff, g)
    else
      -- create
      let (thety, g) := tygen g in
      do name ← fv_new thety, return (name, thety, tt, g)
  else
    let (thety, g) := tygen g in
    do name ← fv_new thety, return (name, thety, tt, g)


-- Returns: (new var, new instruction, std_gen)
def rand_bop (retty:ty) (retvar:string) (bopc:bopcode) (flags:list bopflag) (g:std_gen)
: vars_state (instruction × std_gen) :=
do
  -- choose operand 1
  (varname1, varty1, isfresh1, g) ← choose_or_newvar retty g,
  -- choose operand 2
  -- operand 1 and 2 should have the same type
  (varname2, varty2, isfresh2, g) ← choose_or_newvar varty1 g,
  -- make lhs
  let lhs := reg.r retvar,
  -- create bop.
  let bop := instruction.binop varty1 lhs bopc flags (operand.reg (reg.r varname1))
      (operand.reg (reg.r varname2)),
  return (bop, g)

def rand_icmpop (retvar:string) (cond:icmpcond) (g:std_gen)
: vars_state (instruction × std_gen) :=
do
  -- choose operand 1
  (varname1, varty1, isfresh1, g) ← choose_or_newvar none g,
  -- choose operand 2
  -- operand 1 and 2 should have the same type
  (varname2, varty2, isfresh2, g) ← choose_or_newvar varty1 g,
  -- make lhs
  let lhs := reg.r retvar,
  -- create icmp.
  let iop := instruction.icmpop varty1 lhs cond (operand.reg (reg.r varname1))
      (operand.reg (reg.r varname2)),
  return (iop, g)

def rand_selectop (retty:ty) (retvar:string) (g:std_gen)
: vars_state (instruction × std_gen) :=
do
  -- choose operand 1
  (varname1, varty1, isfresh1, g) ← choose_or_newvar retty g,
  -- choose operand 2
  -- operand 1 and 2 should have the same type
  (varname2, varty2, isfresh2, g) ← choose_or_newvar varty1 g,
  -- choose conditional operand
  (varnamec, vartyc, isfreshc, g) ← choose_or_newvar (ty.int 1) g,
  let selop := instruction.selectop (reg.r retvar)
      vartyc (operand.reg (reg.r varnamec))
      varty1 (operand.reg (reg.r varname1)) (operand.reg (reg.r varname2)) in
  return (selop, g)


def rand_castop (retty:ty) (retvar:string) (castop:uopcode) (fromty:option ty)
    (opname:option string) (g:std_gen)
: vars_state (instruction × std_gen) :=
do
  res:(string × ty × bool × std_gen) ←
    match (opname, fromty) with
    | (none, fromty) := choose_or_newvar fromty g
    | (some r, some fromty) := return (r, fromty, ff, g)
    | _ := sorry
    end,
  let (varname, varty, isfresh, g) := res in
  -- make lhs
  let lhs := reg.r retvar in
  -- create uop
  let uop := instruction.unaryop lhs castop varty (operand.reg (reg.r varname)) retty in
  return (uop, g)


-- Returns: (new freevars, new vars, new instruction, std_gen)
def rand_inst (retty:ty) (retvar:string) (g:std_gen)
: vars_state (instruction × std_gen) :=
  let bops2 := bops.map (λ itm,
    let e := powerset (bop_availflags itm) in
    e.map (λ flags, (itm, flags))) in
  let bops2 := bops2.join in
  let (n, g) := std_next g in
  let n := n % (match retty with
    | ty.int 1 := (bops2.length + uops.length + 1 + icmpconds.length)
    | _ := (bops2.length + uops.length + 1) -- cannot make icmp
    end) in

  if H:(n < bops2.length) then
    let (bopc, flags) := bops2.nth_le n H in
    rand_bop retty retvar bopc flags g

  else
    let n := n - bops2.length in
    if H:(n < uops.length) then
      do
      (fromvar, fromty, isfresh, g) ← choose_or_newvar none g,
      match (fromty, retty) with
      | (ty.int fromsz, ty.int tosz) :=
        if fromsz < tosz then
          let (n, g) := std_next g in
          let castop := if is_even n then uopcode.sext else uopcode.zext in
          rand_castop retty retvar castop fromty fromvar g
        else if fromsz > tosz then
          rand_castop retty retvar uopcode.trunc fromty fromvar g
        else -- no available cast (there's no bitcast yet)
          let tmpop := instruction.binop retty (reg.r retvar) bopcode.add []
                       (operand.reg (reg.r fromvar))
                       (operand.const (const.int 0)) in
          return (tmpop, g)
      | (_, _) := sorry
      end

    else
      let n := n - uops.length in
      if n = 0 then
        do
        rand_selectop retty retvar g
      else
        let n := n - 1 in
        if H:(n < icmpconds.length) then
          let icond := icmpconds.nth_le n H in
          do
          rand_icmpop retvar icond g
        else sorry

-- Returns: a random program
def rand_instlist: nat → ty → string → std_gen →
  vars_state (list instruction × std_gen)
| 0 _ _ g := return ([], g)
| (nat.succ n') retty retvar g :=
  do
  fv_remove retvar,
  (inst, g) ← rand_inst retty retvar g,
  -- randomly choose a free variable.
  ⟨vs, _⟩ ← get,
  if H:(0 < vs.length) then
    do
    let ((nextvar, nextty), g) := pick vs g H,
    (instlist, g) ← rand_instlist n' nextty nextvar g,
    return (instlist ++ [inst], g)
  else
    sorry

def replace_ops (varname:string) (newop:operand) (i:instruction) :=
  let replace (opfrom:operand): operand :=
    match opfrom with
    | operand.reg (reg.r r) := if r = varname then newop else opfrom
    | _ := opfrom
    end in
  match i with
  | instruction.binop retty retvar bopc flags op1 op2 :=
    instruction.binop retty retvar bopc flags (replace op1) (replace op2)
  | instruction.unaryop retvar uopc toty op fromty :=
    instruction.unaryop retvar uopc toty (replace op) fromty
  | instruction.icmpop opty lhs icond op1 op2 :=
    instruction.icmpop opty lhs icond (replace op1) (replace op2)
  | instruction.selectop retvar retty condop condty op1 op2 :=
    instruction.selectop retvar retty (replace condop) condty
      (replace op1) (replace op2)
  end

-- Randomly assigns a constant to free variables
def assign_constants (insts:list instruction) (g:std_gen)
: vars_state (list instruction × std_gen) :=
  do
  vr ← get,
  monad.foldl (λ (data:list instruction × std_gen) (fv:string × ty),
    let (insts, g) := data in
    let (n, g) := std_next g in
    if is_even n then
      -- concretize it!
      do
      let (fvname, fvty) := fv,
      fv_remove fvname, -- remove the free variable.
      let (c, g) := any_const fvty g,
      let insts := insts.map (replace_ops fvname (operand.const (const.int c))),
      return (insts, g)
    else
      return (insts, g)
    ) (insts, g) vr.1

def exec_extension := ".exe"

def refines (final_st: irsem.irstate irsem_exec) (n exitcode:nat): bool :=
  if irsem.irstate.getub irsem_exec final_st = ff then
    tt -- it is already UB
  else if exitcode ≠ 0 then
    ff -- abnormal exit
  else
    let v := irsem.irstate.getreg irsem_exec final_st "%res" in
    match v with
    | none := sorry
    | some v :=
      match v with
      | irsem.valty.ival sz i p :=
        if p = ff then
          tt -- it is already poison
        else i.val = n
      end
    end

-- Runs a single test.
def run_test (clangpath:string) (verbose:bool) (g:std_gen)
: io (bool × std_gen) :=
  let debug_ln (s:string):=
    if verbose then io.print_ln s else return () in
  do
  debug_ln "---------------",
  let (retty, g) := ty_new g,
  -- Create random instructions
  let ((insts, g), vr) :=
      (do (insts, g) ← rand_instlist NUM_INSTS retty "%res" g,
          assign_constants insts g).run vars_record_empty,
  let freevars := vr.1.reverse,
  -- Print the instructions.
  monad.foldl (λ _ inst, debug_ln (to_string inst)) () insts,

  -- Create a random initial state
  let (init_st, g) := freevar.create_init_state_exec freevars g,
  debug_ln "- Initial state",
  let init_st_str := to_string init_st,
  debug_ln init_st_str,

  -- Get the result of it from Lean's semantics.
  debug_ln "- Final state",
  let final_st := irsem.bigstep_exe irsem_exec init_st ⟨insts⟩,
  match final_st with
  | none := do
    io.print_ln "UNREACHABLE!",
    io.print_ln ("INITIAL STATE: " ++ init_st_str),
    return (ff, g)
  | some final_st := do
    let final_st_str := to_string final_st,
    -- Generate LLVM IR
    let ircode := to_llvmir ⟨insts⟩ init_st freevars retty,
    debug_ln "- LLVM IR",
    debug_ln ircode,
    -- store it to a temporary file
    let (tempn, g) := std_next g,
    let tempname := to_string (tempn % 10000000),
    let llname := "./tmp/" ++ tempname ++ ".ll",
    let execname := "./tmp/" ++ tempname ++ exec_extension,
    handler ← io.mk_file_handle llname (io.mode.write) ff,
    io.fs.write handler (ircode.to_list.to_buffer),
    io.fs.close handler,
    child ← io.proc.spawn {
      cmd := clangpath,
      args := ["-o", execname,
        "-Wno-override-module", -- suppress warning
        llname]
    },
    cres ← io.proc.wait child,
    if cres = 0 then do
      -- compilation succeeded.
      child2 ← io.proc.spawn {
        cmd := execname,
        args := [],
        stdout := io.process.stdio.piped
      },
      eout ← io.fs.read_to_end child2.stdout,
      io.fs.close child2.stdout,
      eres ← io.proc.wait child2,
      debug_ln ("output: " ++ eout.to_string),
      let eoutn := (string.to_nat eout.to_string),
      if refines final_st eoutn eres then do
        debug_ln "SUCCESS",
        return (tt, g)
      else do
        io.print_ln "TEST FAIL!",
        monad.foldl (λ _ inst, debug_ln (to_string inst)) () insts,
        io.print_ln ("INITIAL STATE: " ++ init_st_str),
        io.print_ln ("FINAL STATE: " ++ final_st_str),
        io.print_ln ("FILE: " ++ llname ++ " , " ++ execname),
        return (ff, g)
    else do
      io.print_ln "TEST FAIL!",
      monad.foldl (λ _ inst, debug_ln (to_string inst)) () insts,
      io.print_ln ("INITIAL STATE: " ++ init_st_str),
      io.print_ln ("FINAL STATE: " ++ final_st_str),
        io.print_ln ("FILE: " ++ llname ++ " , " ++ execname),
      return (ff, g)
  end

def run_test_n (clangpath:string) (verbose:bool): nat → std_gen → io unit
| 0 g := (return ())
| (nat.succ n') g :=
  do
  if n' % 100 = 0 then
    io.print_ln ("-------" ++ (to_string n') ++ "-------")
  else return (),
  (success, g) ← run_test clangpath verbose g,
  if success then
    run_test_n n' g
  else
    -- stop!
    return ()


meta def main : io unit :=
  let failmsg:io unit := do
      io.print_ln "irtest_run.lean <itrcnt> <clang path> <verbose(y/n)>" in
  do
  args ← io.cmdline_args,
  match args with
  | cnt::clangpath::verbose::_ :=
    let g := mk_std_gen in
    do run_test_n clangpath (verbose = "y") cnt.to_nat g,
    return ()
  | _ := failmsg
  end

-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import system.io
import system.random
import .freevar
import .langparser
import .lang
import .lang_tostr
import .irsem
import .irsem_smt
import .irsem_exec
import .irtype
import .vcgen
import .verifyopt
import smt2.solvers.z3

open io
open parser
open irsem


def string.starts_with (s1:string) (sprefix:string): bool :=
  list.is_prefix_of (sprefix.to_list) (s1.to_list)



def exec_emitter:vcgen.emitter irsem_exec := 
        ⟨irsem_exec.val_to_smt,
        irsem_exec.poison_to_smt, irsem_exec.bool_to_smt⟩

meta def smt_emitter:vcgen.emitter irsem_smt := 
        ⟨irsem_smt.val_to_smt,
        irsem_smt.poison_to_smt, irsem_smt.bool_to_smt⟩

-- Runs a single program.
namespace singleprog

meta def print_result {α:Type} [has_to_string α] (result_state:option α)
  : io (option α) :=
  match result_state with
  | none := do
    io.print_ln "Stuck",
    return none
  | some finalresult := do
    io.print_ln (finalresult),
    return (some finalresult)
  end

-- Executes a program and check whether SMT formula generated
-- from the program encodes the final state.
meta def run_and_emit_smt2 (typedp:program) : io unit :=
  do
  let gen := mk_std_gen,
  print_ln "=== Free Variables ===",
  let freevars := freevar.get typedp,
  print_ln $ "free vars:" ++ to_string freevars,
  print_ln "=== Run-EXE ===",
  let (init_st, gen) := freevar.create_init_state_exec freevars gen,
  final_st ← print_result (bigstep irsem_exec init_st typedp),
  print_ln "=== Run-SMT ===",
  let init_st' := freevar.create_init_state_smt freevars,
  final_st' ← print_result (bigstep irsem_smt init_st' typedp),

  match final_st, final_st' with
  | (some final_st), (some final_st') :=
    do
    print_ln "=== SMT Code Gen ===",
    let smtcode := vcgen.emit_smt typedp
        freevars init_st' final_st final_st'
        exec_emitter smt_emitter,
    print_ln smtcode,
    print_ln "=== Z3 Result ===",
    z3i ← z3_instance.start,
    smtres ← z3_instance.raw z3i smtcode.to_string,
    print_ln smtres,
    return ()
  | _, _ := return ()
  end


-- Reads an input, concretizes its type, emit SMT code, and run it
meta def check (filename:string) (encode_poison:bool): io unit := do
  hl ← mk_file_handle filename (io.mode.read) ff,
  charbuf ← io.fs.read_to_end hl,
  -- Parse the input.
  match (run ReadProgram charbuf) with
  | sum.inl errmsg := put_str errmsg -- Parsing failed.
  | sum.inr prog :=
    let runf := λ p (encode_poison:bool), run_and_emit_smt2 p in
    do
    _ ← put_str (to_string prog),
    match (concretize_type prog) with
    | list.nil := put_str "Cannot find well-typed program with given input."
    | x := -- Just run one among them.
      monad.foldl (λ a typed_prog, do
          print_ln "-------- Next Example ----------",
          print_ln "=== After type concretization ===",
          print_ln typed_prog,
          runf typed_prog encode_poison)
        () x
    end
  end

end singleprog



-- Verifies optimizations.
namespace verifyopt

def root_name (p:program): string :=
  match p.insts.reverse with
  | [] := ""
  | (instruction.binop _ (reg.r r) _ _ _ _)::_ := r
  | (instruction.icmpop _ (reg.r r) _ _ _)::_ := r
  | (instruction.selectop (reg.r r) _ _ _ _ _)::_ := r
  | (instruction.unaryop (reg.r r) _ _ _ _)::_ := r
  end

meta def check_one (t:transformation) (n:nat) (verbose:bool): io unit := do
  let debug_ln (str:format) :=
    if verbose then print_ln str else return (),
  debug_ln format!"--------{t.name}-------{n}--",
  let (lp1, lp2) := (concretize_type t.src, concretize_type t.tgt),
  let gen := mk_std_gen,
  match lp1, lp2 with
  | p1::_, p2::_ := do
    let freevars := freevar.get p1,
    let (init_st, gen) := freevar.create_init_state_exec freevars gen,
    let init_st' := freevar.create_init_state_smt freevars,
    let r := root_name p1,

    debug_ln (format!"Root variable:{r}"),
    debug_ln "=== Does it refine? (EXE) ===",
    let ob_exec := opt.check_single_reg irsem_exec p1 p2 r init_st,
    debug_ln (to_string ob_exec),

    debug_ln "=== Does it refine? (SMT) ===",
    let ob_smt := opt.check_single_reg irsem_smt p1 p2 r init_st',
    debug_ln (to_string ob_smt),

    match ob_smt with
    | some smtobj := do
      debug_ln "=== Z3 Result ===",
      let smtcode := vcgen.emit_refine_smt p1 p2
          freevars smtobj smt_emitter,
      debug_ln smtcode,
      z3i ← z3_instance.start,
      smtres ← z3_instance.raw z3i smtcode.to_string,
      debug_ln (smtres ++ "(Unsat means the opt. is correct)"),
      debug_ln "",
      if smtres = "unsat\n" then
        print_ln "Correct"
      else
        print_ln "Incorrect"
    | none := return ()
    end
  | _, _ := return ()
  end

-- Reads transformations and checks them.
meta def check (filename:string) (parseonly:bool) (verbose:bool): io unit := do
  hl ← mk_file_handle filename (io.mode.read) ff,
  charbuf ← io.fs.read_to_end hl,

  match (run ReadTransformations charbuf) with
  | sum.inl errmsg := put_str errmsg
  | sum.inr tfs :=
    if parseonly then do
      print_ln "Parsing done.",
      _ ← monad.foldl (λ n tf, do
        print_ln (to_string tf), print_ln "", return (n+1)) 1 tfs,
      return ()

    else do
      _ ← monad.foldl (λ n tf, do
        check_one tf n verbose, return (n+1)) 1 tfs,
      return ()
  end

end verifyopt




meta def main : io unit :=
  do args ← io.cmdline_args,
  let cmd := list.head args in
  let args := list.tail args in
  let get_verbose (l:list string): bool :=
    match l with | [] := ff | l :=
    if list.head (list.reverse l) = "-verbose" then tt else ff end in
  match cmd with
  | "-input" := singleprog.check (list.head args) ff
  | "-input2" := singleprog.check (list.head args) tt
  | "-parseopt" := verifyopt.check (list.head args) tt
                    (get_verbose (list.tail args))
  | "-verifyopt" := verifyopt.check (list.head args) ff
                    (get_verbose (list.tail args))
  | _ := print_ln ("Unknown argument: " ++ cmd)
  end
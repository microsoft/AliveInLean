-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import .lang

-- Returns true if program p contains uninstantiated type.
def has_arbitrary_type (p:program): bool :=
  list.foldl (λ (b:bool) inst, bor b
    (match inst with
    | instruction.binop t lhs bop nswnuw op1 op2 :=
        t = ty.arbitrary_int
    | instruction.unaryop r uop t1 op t2 :=
        t1 = ty.arbitrary_int ∨ t2 = ty.arbitrary_int
    | instruction.icmpop t r cond r1 r2 :=
        t = ty.arbitrary_int
    | instruction.selectop r t1 cond t2 op1 op2 :=
        t1 = ty.arbitrary_int ∨ t2 = ty.arbitrary_int
    end)) ff p.insts

-- Returns a list of programs with concretized type
def concretize_type (p:program) : list program :=
  if ¬ (has_arbitrary_type p) then [p]
  else
    let create_one := fun (tysz:nat), program.mk
      ((list.map
        (λ inst, match inst with
        | instruction.binop t lhs bop nswnuw op1 op2 :=
          (instruction.binop
            (match t with
            | ty.arbitrary_int := ty.int tysz
            | _ := t
            end) lhs bop nswnuw op1 op2) -- has type instantiation.
        | _ := inst -- no type instantiation.
        end) (p.insts)):list instruction) in
    [create_one 8, create_one 16]
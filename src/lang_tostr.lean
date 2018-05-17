-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import .lang

namespace const
  instance: has_to_string const :=
  ⟨λ a, match a with
      | (const.int n) := "(int " ++ to_string n ++ ")"
      end⟩
end const

namespace reg
  instance: has_to_string reg :=
  ⟨λ r, match r with
    | (reg.r name) := "(reg " ++ name ++ ")"
    end⟩
end reg

namespace operand
  instance: has_to_string operand :=
  ⟨λ o, match o with
    | (operand.reg r) := to_string r
    | (operand.const c) := to_string c
    end⟩
end operand

namespace ty
  instance: has_to_string ty :=
  ⟨λ t, match t with
    | (ty.int n) := "i" ++ to_string n
    | (ty.arbitrary_int) := "iN"
    end⟩
end ty


instance: has_to_string bopcode :=
⟨(λ l:bopcode, bopcode.rec_on l "add" "sub" "mul" "udiv" "urem" "sdiv" "srem"
  "and" "or" "xor" "shl" "lshr" "ashr")⟩

instance: has_to_string uopcode :=
⟨(λ u:uopcode, uopcode.rec_on u "freeze" "zext" "sext" "trunc")⟩

instance: has_to_string icmpcond :=
⟨(λ u:icmpcond, icmpcond.rec_on u "eq" "ne" "ugt" "uge" "ult" "ule" "sgt" "sge" "slt" "sle")⟩

instance: has_to_string bopflag :=
⟨(λ u:bopflag, bopflag.rec_on u "nsw" "nuw" "exact")⟩


namespace instruction
  instance: has_to_string instruction :=
  ⟨λ i, match i with
    | (instruction.binop lhsty lhs bop flags op1 op2) :=
      (to_string lhs) ++ " = " ++
      (to_string bop) ++
      (list.foldl (λ s1 f, s1 ++ " " ++ to_string f) "" flags) ++ " " ++
      (to_string lhsty) ++ " " ++
      (to_string op1) ++ " " ++ (to_string op2)
    | (instruction.unaryop lhs uop fromty op toty) :=
      (to_string lhs) ++ " = " ++ (to_string uop) ++ " " ++ 
      (match uop with
      | uopcode.freeze := (to_string op)
      | _ := (to_string fromty) ++ " " ++ (to_string op) ++
          " to " ++ (to_string toty)
      end)
    | (instruction.icmpop lhsty lhs cond op1 op2) :=
      (to_string lhs) ++ " = icmp " ++ (to_string cond) ++ " " ++
      (to_string lhsty) ++ " " ++ (to_string op1) ++ (to_string op2)
    | (instruction.selectop lhs condty cond opty op1 op2) :=
      (to_string lhs) ++ " = select " ++ (to_string condty) ++ " " ++
      (to_string cond) ++ ", " ++ (to_string opty) ++ " " ++ (to_string op1) ++
      ", " ++ (to_string opty) ++ " " ++ (to_string op2)
    end⟩
end instruction

namespace program
  instance: has_to_string program :=
  ⟨λ p, list.foldr (λ a b, to_string a ++ "\n" ++ b) "" (p.insts)⟩
end program

namespace transformation
  instance: has_to_string transformation :=
  ⟨λ t, "Name: " ++ t.name ++ "\n" ++ (to_string t.src) ++ "=>\n" ++ (to_string t.tgt)⟩
end transformation
-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

-- constant value
inductive const : Type
| int : ℤ → const

-- register
-- Design choice: Let reg store its name, but not
-- its type. Reason is that, if reg contains type,
-- modifying register's type should track all
-- def-use chains.
inductive reg : Type
| r : string → reg
-- value
inductive operand : Type
| reg : reg → operand
| const : const → operand

-- type
inductive ty : Type
| int : ℕ → ty
| arbitrary_int : ty

-- for (t1:ty) (t2:ty), t1 = t2 is decidable.
instance : decidable_eq ty :=
by tactic.mk_dec_eq_instance

-- binary operation
inductive bopcode : Type
| add | sub | mul | udiv | urem | sdiv | srem | and | or | xor | shl | lshr | ashr

instance : decidable_eq bopcode :=
by tactic.mk_dec_eq_instance
-- Returns true if given bopcode is div or rem
@[reducible, simp]
def bop_isdiv : bopcode → bool
| bopcode.udiv := tt
| bopcode.urem := tt
| bopcode.sdiv := tt
| bopcode.srem := tt
| _ := ff

inductive bopflag : Type
| nsw | nuw | exact

@[reducible]
def bop_availflags : bopcode → list bopflag
| bopcode.add := [bopflag.nsw, bopflag.nuw]
| bopcode.sub := [bopflag.nsw, bopflag.nuw]
| bopcode.mul := [bopflag.nsw, bopflag.nuw]
| bopcode.shl := [bopflag.nsw, bopflag.nuw]
| bopcode.udiv := [bopflag.exact]
| bopcode.sdiv := [bopflag.exact]
| bopcode.urem := []
| bopcode.srem := []
| bopcode.lshr := [bopflag.exact]
| bopcode.ashr := [bopflag.exact]
| bopcode.and := []
| bopcode.or := []
| bopcode.xor := []

-- icmp operation
inductive icmpcond : Type
| eq | ne | ugt | uge | ult | ule | sgt | sge | slt | sle

-- unary operation
inductive uopcode : Type
| freeze | zext | sext | trunc

-- instruction
-- TODO: the order of parameters should be consistent
inductive instruction : Type
-- binop: operations in https://github.com/nunoplopes/alive/blob/newsema/language.py#L278
| binop : ty → reg → bopcode → list bopflag →
          operand → operand → instruction
| icmpop : ty → reg → icmpcond → operand → -- opty, lhs, cond, op1, op2
           operand → instruction
| selectop : reg → ty → operand → ty → operand → -- condty, opty
             operand → instruction
| unaryop : reg → uopcode →
            ty → operand → ty → instruction -- fromty, toty

-- program
structure program : Type := 
(insts: list instruction)

-- transformation
structure transformation : Type :=
(name:string)
(src:program)
(tgt:program)

-- precondition
mutual inductive precond_fun, precond_exp
with precond_fun : Type
-- isPower2(x): returns true if x is guaranteed to
--              be power of 2, returns false otherwise
| is_power2 : precond_exp → precond_fun
-- mayAlias(p, q): returns true if p and q may alias.
--                 If p and q are guaranteed not to alias,
--                 it returns false.
| may_alias : precond_exp → precond_exp → precond_fun
with precond_exp : Type
-- E1 && E2, E1 & E2
-- E1 and E2 may be either bool or int type.
| and : precond_exp → precond_exp → precond_exp
-- E1 || E2, E1 | E2
-- E1 and E2 may be either bool or int type.
| or : precond_exp → precond_exp → precond_exp
-- ~E
-- E may be either bool or int type.
| not : precond_exp → precond_exp
-- Value (register or constant)
| v : operand → precond_exp
-- Function call
| fcall : precond_fun → precond_exp

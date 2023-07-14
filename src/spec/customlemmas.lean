import ..lang
import ..irsem
import ..irsem_exec
import .lemmas_basic
import .lemmas

open irsem_exec

-- a single small-step function
@[simp]
def step := irsem.step irsem_exec

-- a new udiv instruction
@[simp]
def udiv (isz:nat) (name:string) (op1 op2:operand): instruction
  := instruction.binop (ty.int isz) (reg.r name) (bopcode.udiv) [] op1 op2

-- ub check
@[simp]
def has_ub (st:irsem.irstate irsem_exec):Prop :=
  irsem.irstate.getub irsem_exec st = ff

-- get value
@[simp]
def get_value (st:irsem.irstate irsem_exec) (op:operand) (opty:ty) :=
  irsem.get_value irsem_exec st op opty

-- is poison?
@[simp]
def is_poison: irsem.valty irsem_exec → Prop
| (irsem.valty.ival sz o b) :=
  b = (@bool_like.ff irsem_exec.poisonty irsem_exec.pbl)

set_option eqn_compiler.zeta true
set_option pp.proofs true

local attribute [simp] option.bind irsem.step irsem.step_bop
  irsem.bop irsem.bop_ub irsem.irstate.updateub irsem.irstate.updatereg

lemma never_poison:
  ∀ isz name op1 op2 st st' val
    (HSTEP:step st (udiv isz name op1 op2) = some st')
    (HNOUB:¬ has_ub st')
    (HVAL:some val = get_value st op2 (ty.int isz)),
  ¬ is_poison val
:= begin
  intros,
  cases st with ub regs, cases st' with ub' regs',
  cases ub'; simp at HNOUB; unfold irsem.irstate.getub at HNOUB,
    injection HNOUB, clear HNOUB,
  cases op2, simp at *,
  {
    cases (irsem.get_value irsem_exec (ub, regs) op1 (ty.int isz)) with val1;
      unfold has_bind.bind at *; unfold option.bind at *,
    injection HSTEP,
    rw ← HVAL at HSTEP, simp at HSTEP,
    cases val1 with isz1 ii1 ip1,
    cases val with isz2 ii2 ip2,
    simp at HSTEP,
    have HISZDEC:decidable (isz1 = isz2), apply_instance,
    cases HISZDEC; unfold irsem.bop_val at HSTEP,
    { rw dif_neg at HSTEP, injection HSTEP },
    { rw (dif_pos HISZDEC) at HSTEP,
      injection HSTEP with HSTEP', clear HSTEP,
      cases ub; cases ip2,
      any_goals {
        -- if dividend was poison or previous state was ub..
        unfold_coes at HSTEP', unfold has_and.and at HSTEP',
        unfold bool_like.and at HSTEP', simp at HSTEP', cases HSTEP' with HH _ },
      { simp }
    }
  },
  {
    simp at HVAL,
    cases op2,
    unfold irsem.get_value at HVAL,
    have HSZDEC1: decidable (0 < isz), apply_instance,
    cases HSZDEC1,
    { rw (dif_neg HSZDEC1) at HVAL, injection HVAL },
    { rw (dif_pos HSZDEC1) at HVAL,
      simp at HVAL,
      have HVAL2 := ite_or _ HVAL,
      cases HVAL2,
      { injection HVAL2, rw h_1, simp },
      { have HVAL3 := ite_or _ HVAL2,
        cases HVAL3,
        { injection HVAL3, rw h_1, simp },
        { injection HVAL3 }
      }
    }
  }
end
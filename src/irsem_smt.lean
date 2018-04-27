import system.io
import smt2.syntax
import smt2.builder
import .irsem
import .lang
import .common
import .bitvector
import .smtexpr
import .smtcompile
open io

def irsem_smt : irsem := { intty := sbitvec, poisonty := sbool, boolty := sbool }

namespace irsem_smt
  open irsem
  local attribute [reducible] irsem_smt

  @[reducible] instance iul: uint_like irsem_smt.intty := sbitvec_is_uint_like
  @[reducible] instance ihc: has_comp irsem_smt.intty irsem_smt.boolty := sbitvec_has_comp
  @[reducible] instance ioc: has_overflow_check irsem_smt.intty irsem_smt.boolty :=
      sbitvec_has_overflow_check
  @[reducible] instance pbl: bool_like irsem_smt.poisonty := sbool_is_bool_like
  @[reducible] instance p2b: has_coe irsem_smt.poisonty irsem_smt.boolty := ⟨@id sbool⟩
  @[reducible] instance bbl: bool_like irsem_smt.boolty := sbool_is_bool_like
  @[reducible] instance b2i: has_coe irsem_smt.boolty (irsem_smt.intty size.one) := sbool_sbitvec_has_coe
  @[reducible] instance bhi (sz:size): has_ite irsem_smt.boolty (irsem_smt.intty sz) := sbitvec_has_ite
  @[reducible] instance bhi2 : has_ite irsem_smt.boolty irsem_smt.poisonty := sbool_has_ite


  meta instance poisonty_tostr: has_to_string irsem_smt.poisonty :=
  ⟨λ b:sbool, to_string b⟩
  meta instance valty_tostr: has_to_string irsem_smt.valty :=
  ⟨λ b, match b with
  | (irsem.valty.ival sz b p) := has_to_string.to_string b ++
      ", IS_NOT_POISON:" ++ to_string p
  end⟩
  meta instance boolty_tostr: has_to_string irsem_smt.boolty :=
  ⟨λ b:sbool, to_string b⟩

  meta instance tostr: has_to_string irsem_smt.irstate :=
  ⟨λ st, irstate.to_string' irsem_smt st⟩

  meta def int_to_smt (sz:size) : irsem_smt.intty sz → smt2.term
  | x := smt.compile_sbitvec x
  meta def val_to_smt : irsem_smt.valty → smt2.term
  | (irsem.valty.ival sz t _) := int_to_smt sz t
  meta def poison_to_smt : irsem_smt.valty → smt2.term
  | (irsem.valty.ival _ _ p) := smt.compile_sbool p
  meta def bool_to_smt : irsem_smt.boolty → smt2.term
  | u := smt.compile_sbool u
end irsem_smt

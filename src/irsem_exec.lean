-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import system.io
import smt2.syntax
import .irsem
import .lang
import .common
import .bitvector

open io

-- poisonty := bool -- If it is false, it is poison.
-- boolty := bool -- If it is false, it is UB.
def irsem_exec : irsem := { intty := bitvector, poisonty := bool, boolty := bool }

namespace irsem_exec
  open irsem

  @[reducible] instance iul: uint_like irsem_exec.intty := bitvector_is_uint_like
  @[reducible] instance ihc: has_comp irsem_exec.intty irsem_exec.boolty := bitvector_has_comp
  @[reducible] instance ioc: has_overflow_check irsem_exec.intty irsem_exec.boolty :=
      bitvector_has_overflow_check
  @[reducible] instance pbl: bool_like irsem_exec.poisonty := bool_is_bool_like
  @[reducible] instance p2b: has_coe irsem_exec.poisonty irsem_exec.boolty := ⟨@id bool⟩
  @[reducible] instance bbl: bool_like irsem_exec.boolty := bool_is_bool_like
  @[reducible] instance b2i: has_coe irsem_exec.boolty (irsem_exec.intty size.one) := bool_bitvec_has_coe
  @[reducible] instance bhi (sz:size): has_ite irsem_exec.boolty (irsem_exec.intty sz) := bool_has_ite (bitvector sz)
  @[reducible] instance bhi2 : has_ite irsem_exec.boolty irsem_exec.poisonty := bool_has_ite irsem_exec.poisonty

  def give_poison: irsem.valty irsem_exec → irsem.valty irsem_exec
  | (valty.ival sz o b) := valty.ival sz o
        (@bool_like.ff irsem_exec.poisonty irsem_exec.pbl)

  instance poisonty_tostr: has_to_string irsem_exec.poisonty :=
  ⟨λ b:bool, to_string b⟩
  instance valty_tostr: has_to_string irsem_exec.valty :=
  ⟨λ b, match b with
  | (irsem.valty.ival sz b p) := has_to_string.to_string (b.1) ++
      ", poison:" ++ to_string (~p)
  end⟩
  instance boolty_tostr: has_to_string irsem_exec.boolty :=
  ⟨λ b:bool, to_string b⟩

  instance tostr: has_to_string irsem_exec.irstate :=
  ⟨λ st, irstate.to_string' irsem_exec st⟩

  def int_to_smt (sz:size) : irsem_exec.intty sz → smt2.term
  | z := smt2.term.const (smt2.special_constant.bitvec sz z.1)
  def val_to_smt : irsem_exec.valty → smt2.term
  | (irsem.valty.ival sz i _) := int_to_smt sz i
  def poison_to_smt : irsem_exec.valty → smt2.term
  | (irsem.valty.ival _ _ p) := smt2.term.const (smt2.special_constant.bool p)
  def bool_to_smt : irsem_exec.boolty → smt2.term
  | p := smt2.term.const (smt2.special_constant.bool p)
end irsem_exec

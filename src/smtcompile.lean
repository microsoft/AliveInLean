-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import .smtexpr
import smt2.syntax
import smt2.builder

namespace smt

-- A sample optimizing function.
@[reducible] def optimize_add_zero {sz:size} : sbitvec sz → sbitvec sz
| (sbitvec.add (sbitvec.const _ 0) y) := y
| s := s

open sbitvec
open sbool
open smt2.builder

mutual def compile_sbitvec, compile_sbool
with compile_sbitvec : Π {sz:size}, sbitvec sz → smt2.term
| _ (const sz n) := smt2.term.const (smt2.special_constant.bitvec sz (n))
| _ (var sz x) := smt2.term.qual_id x
| _ (add x y) := bv_add (compile_sbitvec x) (compile_sbitvec y)
| _ (sub x y) := bv_sub (compile_sbitvec x) (compile_sbitvec y)
| _ (mul x y) := bv_mul (compile_sbitvec x) (compile_sbitvec y)
| _ (udiv x y) := bv_udiv (compile_sbitvec x) (compile_sbitvec y)
| _ (urem x y) := bv_urem (compile_sbitvec x) (compile_sbitvec y)
| _ (sdiv x y) := bv_sdiv (compile_sbitvec x) (compile_sbitvec y)
| _ (srem x y) := bv_srem (compile_sbitvec x) (compile_sbitvec y)
| _ (and x y) := bv_and (compile_sbitvec x) (compile_sbitvec y)
| _ (or x y) := bv_or (compile_sbitvec x) (compile_sbitvec y)
| _ (xor x y) := bv_xor (compile_sbitvec x) (compile_sbitvec y)
| _ (shl x y) := bv_shl (compile_sbitvec x) (compile_sbitvec y)
| _ (lshr x y) := bv_lshr (compile_sbitvec x) (compile_sbitvec y)
| _ (ashr x y) := bv_ashr (compile_sbitvec x) (compile_sbitvec y)
| _ (@zext sz sz' x) := bv_zext (sz'- sz) (@compile_sbitvec sz x)
| _ (@sext sz sz' x) := bv_sext (sz'- sz) (@compile_sbitvec sz x)
| _ (@trunc sz sz' x) := bv_extract (sz'-1) 0 (@compile_sbitvec sz x)
| _ (@extract sz sz' hb lb H x) := bv_extract hb lb (@compile_sbitvec sz x)
| _ (@sbitvec.ite sz cond x y) := ite (compile_sbool cond) (compile_sbitvec x) (compile_sbitvec y)
with compile_sbool: sbool → smt2.term
| tt := smt2.term.const (smt2.special_constant.bool tt)
| ff := smt2.term.const (smt2.special_constant.bool ff)
| (var x) := smt2.term.qual_id x
| (and x y) := and2 (compile_sbool x) (compile_sbool y)
| (or x y) := or2 (compile_sbool x) (compile_sbool y)
| (xor x y) := xor2 (compile_sbool x) (compile_sbool y)
| (eqb x y) := equals (compile_sbool x) (compile_sbool y)
| (neb x y) := equals (compile_sbool x) (compile_sbool y)
| (ite c x y) := ite (compile_sbool c) (compile_sbool x) (compile_sbool y)
| (not x) := not (compile_sbool x)
| (@eqbv sz x y) :=
    have Hx: 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    have Hy: 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    equals (compile_sbitvec x) (compile_sbitvec y)
| (@nebv sz x y) := 
    have Hx: 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    have Hy: 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    not (equals (compile_sbitvec x) (compile_sbitvec y))
| (@sle sz x y) := 
    have Hx: 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    have Hy: 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    bv_sle (compile_sbitvec x) (compile_sbitvec y)
| (@slt sz x y) := 
    have Hx: 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    have Hy: 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    bv_slt (compile_sbitvec x) (compile_sbitvec y)
| (@ule sz x y) := 
    have Hx: 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    have Hy: 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    bv_ule (compile_sbitvec x) (compile_sbitvec y)
| (@ult sz x y) := 
    have Hx: 0 < sbitvec.sizeof sz x, by apply sbitvec.decr_sbitvec,
    have Hy: 0 < sbitvec.sizeof sz y, by apply sbitvec.decr_sbitvec,
    bv_ult (compile_sbitvec x) (compile_sbitvec y)


meta instance sbool_has_to_string : has_to_string sbool :=
⟨λ b, to_string ((compile_sbool b).to_format) ⟩
meta instance sbitvec_has_to_string {sz:size} : has_to_string (sbitvec sz) :=
⟨λ b, to_string ((compile_sbitvec b).to_format) ⟩

end smt
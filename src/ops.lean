-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import .common

universes u v

class has_udiv  (α : Type u) := (udiv : α → α → α)
class has_umod  (α : Type u) := (umod : α → α → α)
class has_and   (α : Type u) := (and : α → α → α)
class has_or    (α : Type u) := (or : α → α → α)
class has_xor   (α : Type u) := (xor : α → α → α)
class has_shl   (α : Type u) := (shl : α → α → α)
class has_lshr    (α : Type u) := (lshr : α → α → α)
class has_ashr   (α : Type u) := (ashr : α → α → α)
class has_not   (α : Type u) := (not : α → α)
infix `/u`:70 := has_udiv.udiv
infix `%u`:70 := has_umod.umod
infix `&`:70 := has_and.and
infix `|b`:70 := has_or.or
infix `^b`:70 := has_xor.xor
infix `<<`:70 := has_shl.shl
infix `>>l`:70 := has_lshr.lshr
infix `>>a`:70 := has_ashr.ashr
prefix `~` := has_not.not

class has_eq  (β: Type v) (α: Type u) := (eq : α → α → β)
class has_ne  (β: Type v) (α: Type u) := (ne : α → α → β)
class has_slt  (β: Type v) (α: Type u) := (slt : α → α → β)
class has_sle  (β: Type v) (α: Type u) := (sle : α → α → β)
class has_ult  (β: Type v) (α: Type u) := (ult : α → α → β)
class has_ule  (β: Type v) (α: Type u) := (ule : α → α → β)
class has_sgt  (β: Type v) (α: Type u) := (sgt : α → α → β)
class has_sge  (β: Type v) (α: Type u) := (sge : α → α → β)
class has_ugt  (β: Type v) (α: Type u) := (ugt : α → α → β)
class has_uge  (β: Type v) (α: Type u) := (uge : α → α → β)

notation a `=_{` ty `}` b : 50 := has_eq.eq ty a b
notation a `≠_{` ty `}` b : 50 := has_ne.ne ty a b
notation a `<_{` ty `}` b : 50 := has_slt.slt ty a b
notation a `≤_{` ty `}` b : 50 := has_sle.sle ty a b
notation a `>_{` ty `}` b : 50 := has_sgt.sgt ty a b
notation a `≥_{` ty `}` b : 50 := has_sge.sge ty a b
notation a `<u_{` ty `}` b : 50 := has_ult.ult ty a b
notation a `≤u_{` ty `}` b : 50 := has_ule.ule ty a b
notation a `>u_{` ty `}` b : 50 := has_ugt.ugt ty a b
notation a `≥u_{` ty `}` b : 50 := has_uge.uge ty a b

class bool_like (α: Type u) :=
  (tt ff:α)
  (and or xor:α → α → α)
  (not:α → α)

instance bool_like_has_and (α : Type u) [s:bool_like α]
: has_and α := ⟨s.and⟩
instance bool_like_has_or (α : Type u) [s:bool_like α]
: has_or α := ⟨s.or⟩
instance bool_like_has_xor (α : Type u) [s:bool_like α]
: has_xor α := ⟨s.xor⟩
instance bool_like_has_not (α : Type u) [s:bool_like α]
: has_not α := ⟨s.not⟩

instance bool_is_bool_like : bool_like bool :=
⟨tt, ff, band, bor, bxor, bnot⟩


class uint_like (α: Π (v:size), Type v) :=
    (add sub mul udiv urem sdiv srem and or xor shl lshr ashr:
      Π {sz:size}, α sz → α sz → α sz)
  (zero {} :Π (sz:size), α sz)
  (allone {} :Π (sz:size), α sz)
  (signonly {} :Π (sz:size), α sz)
  (from_z {} :Π (sz:size) (z:ℤ), α sz)
  (zext sext:Π (sz1 sz2:size), α sz1 → α sz2)
  (trunc:Π (sz1 sz2:size), α sz1 → α sz2)

instance uint_like_has_add (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_add (α sz) := ⟨uint_like.add⟩
instance uint_like_has_sub (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_sub (α sz) := ⟨uint_like.sub⟩
instance uint_like_has_mul (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_mul (α sz) := ⟨uint_like.mul⟩
instance uint_like_has_udiv (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_udiv (α sz) := ⟨uint_like.udiv⟩
instance uint_like_has_urem (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_umod (α sz) :=
⟨uint_like.urem⟩ -- Even if rem and mod are different, we define this way
        -- because this helps us use '%u' operator
instance uint_like_has_sdiv (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_div (α sz) := ⟨uint_like.sdiv⟩
instance uint_like_has_srem (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_mod (α sz) := ⟨uint_like.srem⟩
instance uint_like_has_and (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_and (α sz) := ⟨uint_like.and⟩
instance uint_like_has_or (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_or (α sz) := ⟨uint_like.or⟩
instance uint_like_has_xor (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_xor (α sz) := ⟨uint_like.xor⟩
instance uint_like_has_shl (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_shl (α sz) := ⟨uint_like.shl⟩
instance uint_like_has_lshr (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_lshr (α sz) := ⟨uint_like.lshr⟩
instance uint_like_has_ashr (α:Π (v:size), Type v) [s:uint_like α] {sz:size}
: has_ashr (α sz) := ⟨uint_like.ashr⟩


class has_ite (α :Type v) (β:Type u) :=
  (ite:α → β → β → β)

@[reducible]
instance bool_has_ite (β:Type u) : has_ite bool β :=
⟨cond⟩

class has_comp (α:Π (v:size), Type u) (β:Type v) :=
  (eq ne sle slt ule ult:Π {sz:size}, α sz → α sz → β)

instance has_comp_has_eq (α:Π (v:size), Type u) (β:Type v) [s:has_comp α β] {sz:size}
: has_eq β (α sz) := ⟨@has_comp.eq α β s sz⟩
instance has_comp_has_ne (α:Π (v:size), Type u) (β:Type v) [s:has_comp α β] {sz:size}
: has_ne β (α sz) := ⟨@has_comp.ne α β s sz⟩
instance has_comp_has_slt (α:Π (v:size), Type u) (β:Type v) [s:has_comp α β] {sz:size}
: has_slt β (α sz) := ⟨@has_comp.slt α β s sz⟩
instance has_comp_has_sle (α:Π (v:size), Type u) (β:Type v) [s:has_comp α β] {sz:size}
: has_sle β (α sz) := ⟨@has_comp.sle α β s sz⟩
instance has_comp_has_sgt (α:Π (v:size), Type u) (β:Type v) [s:has_comp α β] {sz:size}
: has_sgt β (α sz) := ⟨λ x y, has_comp.slt β y x⟩
instance has_comp_has_sge (α:Π (v:size), Type u) (β:Type v) [s:has_comp α β] {sz:size}
: has_sge β (α sz) := ⟨λ x y, has_comp.sle β y x⟩
instance has_comp_has_ult (α:Π (v:size), Type u) (β:Type v) [s:has_comp α β] {sz:size}
: has_ult β (α sz) := ⟨@has_comp.ult α β s sz⟩
instance has_comp_has_ule (α:Π (v:size), Type u) (β:Type v) [s:has_comp α β] {sz:size}
: has_ule β (α sz) := ⟨@has_comp.ule α β s sz⟩
instance has_comp_has_ugt (α:Π (v:size), Type u) (β:Type v) [s:has_comp α β] {sz:size}
: has_ugt β (α sz) := ⟨λ x y, has_comp.ult β y x⟩
instance has_comp_has_uge (α:Π (v:size), Type u) (β:Type v) [s:has_comp α β] {sz:size}
: has_uge β (α sz) := ⟨λ x y, has_comp.ule β y x⟩


class has_overflow_check (α:Π (v:size), Type u) (β:Type v):=
  (add_chk sub_chk mul_chk shl_chk:Π {sz:size}, bool → α sz → α sz → β) -- is_sign? → op1 → op2 

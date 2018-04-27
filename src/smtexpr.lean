import .common
import .ops
import .bitvector
import smt2.syntax
import smt2.builder

universes u

mutual inductive sbool, sbitvec
with sbool : Type
| tt: sbool | ff:sbool
| var: string → sbool -- unbound variable
| and: sbool → sbool → sbool
| or: sbool → sbool → sbool
| xor: sbool → sbool → sbool
| eqb: sbool → sbool → sbool
| neb: sbool → sbool → sbool
| ite: sbool → sbool → sbool → sbool
| not: sbool → sbool
| eqbv: Π {sz:size}, sbitvec sz → sbitvec sz → sbool
| nebv: Π {sz:size}, sbitvec sz → sbitvec sz → sbool
| sle: Π {sz:size}, sbitvec sz → sbitvec sz → sbool
| slt: Π {sz:size}, sbitvec sz → sbitvec sz → sbool
| ule: Π {sz:size}, sbitvec sz → sbitvec sz → sbool
| ult: Π {sz:size}, sbitvec sz → sbitvec sz → sbool
with sbitvec : size → Type
| const: Π (sz:size) (n:nat), sbitvec sz
| var: Π (sz:size), string → sbitvec sz -- unbound variable
| add: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| sub: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| mul: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| udiv: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| urem: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| sdiv: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| srem: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| and: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| or: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| xor: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| shl: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| lshr: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| ashr: Π {sz:size}, sbitvec sz → sbitvec sz → sbitvec sz
| zext: Π {sz:size} (sz':size), sbitvec sz → sbitvec sz'
| sext: Π {sz:size} (sz':size), sbitvec sz → sbitvec sz'
| trunc: Π {sz:size} (sz':size), sbitvec sz → sbitvec sz'
| extract: Π {sz sz':size} (highbit lowbit:nat)
    (H:sz'.val = highbit - lowbit + 1), sbitvec sz → sbitvec sz'
| ite: Π {sz:size}, sbool → sbitvec sz → sbitvec sz → sbitvec sz


namespace sbool

open smt2.term
open smt2.builder

def of_bool (b:bool):sbool :=
  cond b sbool.tt sbool.ff

def and_simpl (t1 t2:sbool):sbool :=
match t1 with
| sbool.tt := t2
| sbool.ff := sbool.ff
| _ :=
  match t2 with
  | sbool.tt := t1
  | sbool.ff := sbool.ff
  | _ := sbool.and t1 t2
  end
end

end sbool

instance sbool_is_bool_like : bool_like sbool :=
⟨sbool.tt, sbool.ff, sbool.and, sbool.or, sbool.xor, sbool.not⟩

instance sbool_has_ite : has_ite sbool sbool :=
⟨sbool.ite⟩



namespace sbitvec

open smt2.term
open smt2.builder

def of_int (sz:size) : ℤ → sbitvec sz
| x@(int.of_nat q) := sbitvec.const sz (q % (2^sz.val))
| x@(int.neg_succ_of_nat p) :=
  sbitvec.const sz (((2 ^ sz.val) - p - 1) % (2^sz.val))

def one (sz:size) : sbitvec sz := of_int sz 1

def zero (sz:size) : sbitvec sz := of_int sz 0

def intmin (sz:size) : sbitvec sz := of_int sz (int_min_nat sz)

def intmax (sz:size) : sbitvec sz := of_int sz (int.of_nat ((2^(sz.val-1))-1))

def uintmax (sz:size) : sbitvec sz := of_int sz (all_one_nat sz)

def of_bool (b:sbool) : sbitvec (size.one) :=
    sbitvec.ite b (sbitvec.one size.one) (sbitvec.zero size.one)

def of_bv {sz:size} (b:bitvector sz) : sbitvec sz := of_int sz b.1

private theorem add_size_eq (n m:size):
  subtype.mk ((n.1 + m.1 - 1) - n.1 + 1) dec_trivial = m :=
begin apply subtype.eq, simp,
  rewrite nat.add_sub_assoc,
  { -- 1 + (n.val + (m.val - 1) - n.val) = m.val
    rewrite nat.add_sub_cancel_left, -- 1 + (m.val - 1) = m.val
    rewrite ← nat.add_sub_assoc, -- 1 + m.val - 1 = m.val
    rewrite nat.add_sub_cancel_left, -- 1 ≤ m.val
    apply m.2
  },
  { -- 1 ≤ m.val
    apply m.2 }
end

theorem decr_sbitvec: ∀ (sz:size) (v:sbitvec sz), 0 < sbitvec.sizeof sz v
:= begin
  intros, induction v,
  any_goals { unfold sbitvec.sizeof, try {simp}, rw nat.one_add, exact dec_trivial }
end

variable {sz:size}

def mk_zext (m:size) (a:sbitvec sz): sbitvec (sz.add m) :=
  sbitvec.zext (sz.add m) a

def mk_sext (m:size) (a:sbitvec sz): sbitvec (sz.add m) :=
  sbitvec.sext (sz.add m) a

-- Returns false if it overflows.
def overflow_chk (f:Π {sz':size}, sbitvec sz' → sbitvec sz' → sbitvec sz')
    (m:size) (signed:bool)
    (a b:sbitvec sz):sbool :=
  if signed then
    let a'  := sbitvec.mk_sext m a,
        b'  := sbitvec.mk_sext m b,
        r'  := f a' b',
        r   := f a  b,
        r'' := sbitvec.mk_sext m r in
    sbool.nebv r' r''
  else
    let a' := sbitvec.mk_zext m a,
        b' := sbitvec.mk_zext m b,
        r'  := f a' b' in
    let H:(m.val = (sz.val + m.val - 1) - sz.val + 1) := begin
      rw nat.add_comm sz.val m.val,
      rw nat.sub.right_comm,
      rw nat.add_sub_cancel,
      rw nat.sub_add_cancel,
      cases m, assumption
    end in
    let padding := sbitvec.extract (sz+m-1) sz H r' in
    sbool.nebv padding (sbitvec.zero m)

def shl_overflow_chk (m:size) (signed:bool) (a b:sbitvec sz):sbool :=
  overflow_chk (@sbitvec.shl) sz signed a (sbitvec.urem b (sbitvec.of_int sz sz.val))
end sbitvec


instance sbitvec_is_uint_like
: uint_like (sbitvec) :=
⟨@sbitvec.add, @sbitvec.sub, @sbitvec.mul,
  @sbitvec.udiv, @sbitvec.urem, @sbitvec.sdiv, @sbitvec.srem,
  @sbitvec.and, @sbitvec.or, @sbitvec.xor,
  @sbitvec.shl, @sbitvec.lshr, @sbitvec.ashr,
  sbitvec.zero, sbitvec.uintmax, sbitvec.intmin,
  sbitvec.of_int, @sbitvec.zext, @sbitvec.sext, @sbitvec.trunc⟩

instance sbool_sbitvec_has_coe: has_coe sbool (sbitvec size.one) :=
⟨sbitvec.of_bool⟩

@[reducible]
instance sbitvec_has_comp
: has_comp sbitvec sbool :=
⟨@sbool.eqbv, @sbool.nebv, @sbool.sle, @sbool.slt, @sbool.ule, @sbool.ult⟩

instance sbitvec_has_ite {sz:size} : has_ite sbool (sbitvec sz) :=
⟨sbitvec.ite⟩

instance sbitvec_has_overflow_check
: has_overflow_check sbitvec sbool :=
⟨(λ {sz:size}, @sbitvec.overflow_chk sz @sbitvec.add size.one),
(λ {sz:size}, @sbitvec.overflow_chk sz @sbitvec.sub size.one),
(λ {sz:size}, @sbitvec.overflow_chk sz @sbitvec.mul sz),
(λ {sz:size}, @sbitvec.shl_overflow_chk sz sz)⟩

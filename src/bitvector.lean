import .common
import .ops

def bitvector (sz:size) :=
{ x : nat // x < (2 ^ sz.val) }

instance (sz:size) : has_to_string (bitvector sz) :=
⟨λ s, to_string s.1⟩

instance (sz:size) : has_zero (bitvector sz) :=
⟨⟨0, -- 0 < sz → 0 < sz^n
  nat.pos_pow_of_pos sz dec_trivial⟩⟩

instance (sz:size): has_coe (bitvector sz) nat :=
⟨λ s, s.1⟩


namespace bitvector

private lemma nat.ne_zero_of_pos {n:ℕ} : n > 0 → n ≠ 0 := 
λ h contr, by simp [contr] at h; cases h

lemma bv_mod_lt (n : nat) (sz : nat) : n % (2^sz) < 2^sz :=
begin
    apply nat.mod_lt,
    apply nat.pos_pow_of_pos,
    tactic.comp_val
end

local notation `♯` := by apply bv_mod_lt


def to_int {sz:size} (x:bitvector sz) : ℤ :=
  if x.1 < (2 ^ (sz.val - 1)) then x.1
  else int.neg_succ_of_nat (2 ^ sz.val - x.1 - 1)

def of_int (sz:size) : ℤ → bitvector sz
| x@(int.of_nat q) :=
  ⟨q % (2 ^ sz.val), ♯⟩
| x@(int.neg_succ_of_nat p) :=
  ⟨(((2 ^ sz.val) - p - 1) % (2^sz.val)), ♯⟩

def all_one (sz:size) : bitvector sz := of_int sz (all_one_nat sz)

def int_min (sz:size) : bitvector sz := of_int sz (int_min_nat sz)

def zero (sz:size) : bitvector sz := of_int sz 0

def of_bool (b:bool) : bitvector (size.one) := of_int size.one (cond b 1 0)

variable {sz:size}

def signed_check (b1 b2:bitvector sz) (f:ℤ → ℤ → ℤ) : bool :=
  let i1 := to_int b1,
    i2 := to_int b2,
    s  := int.of_nat (2^(sz.val - 1)) in
  f i1 i2 < 0 - s ∨ s ≤ f i1 i2
def unsigned_check (b1 b2:bitvector sz) (f:ℤ → ℤ → ℤ) : bool :=
  let i1:ℤ := b1,
    i2:ℤ := b2,
    s    := int.of_nat (2 ^ sz.val) in
  f i1 i2 < 0 ∨ s ≤ f i1 i2


def add (b1 b2:bitvector sz) : bitvector sz :=
  ⟨(b1 + b2) % (2 ^ sz.val), ♯⟩

def add_overflows (signed:bool) (b1 b2:bitvector sz) : bool :=
  if signed then signed_check b1 b2 int.add
  else unsigned_check b1 b2 int.add

def sub (b1 b2:bitvector sz) : bitvector sz :=
  ⟨(b1 + (2 ^ sz.val) - b2) % (2 ^ sz.val), ♯⟩

def sub_overflows (signed:bool) (b1 b2:bitvector sz) : bool :=
  if signed then signed_check b1 b2 (λ i1 i2, int.add i1 (0-i2))
  else unsigned_check b1 b2 (λ i1 i2, int.add i1 (0-i2))

def mul (b1 b2:bitvector sz) : bitvector sz :=
  ⟨(b1 * b2) % (2 ^ sz.val), ♯⟩
def mul_overflows (signed:bool) (b1 b2:bitvector sz) : bool :=
  if signed then signed_check b1 b2 int.mul
  else unsigned_check b1 b2 int.mul

-- Returns 0 in case of division by zero
def udiv (b1 b2:bitvector sz) : bitvector sz :=
  ⟨(b1 / b2) % (2 ^ sz.val), ♯⟩

-- Returns 0 in case of division by zero
def urem (b1 b2:bitvector sz) : bitvector sz :=
  ⟨(b1 % b2) % (2 ^ sz.val), ♯⟩

-- Returns 0 in case of division by zero.
-- Returns 0 in case of INT_MIN / -1.
def sdiv (b1 b2:bitvector sz) : bitvector sz :=
  of_int sz (int.quot (to_int b1) (to_int b2))

-- Returns 0 in case of division by zero.
def srem (b1 b2:bitvector sz) : bitvector sz :=
  of_int sz (int.rem (to_int b1) (to_int b2))

-- Utility functions for bitwise operations.
def bits_to_nat (v : list bool) : ℕ :=
list.foldr (λ (b:bool) (x:ℕ), 2 * x + cond b 1 0) 0 v

def nat_to_bits : Π (sz:ℕ), ℕ → list bool
| 0 n       := []
| (nat.succ sz') n := to_bool (n % 2 = 1) :: (nat_to_bits sz' (n / 2))

def list_bitwise_op (f:bool → bool → bool) : ∀ (l1 l2: list bool), list bool
| (h1::t1) (h2::t2) := ((f h1 h2)::(list_bitwise_op t1 t2))
| (list.nil) (list.nil) := []
| _ _ := []

-- bitwise operation template.
def bitwise_op (f:bool → bool → bool) (b1 b2:bitvector sz) : bitvector sz :=
  ⟨bits_to_nat (list_bitwise_op f (nat_to_bits sz b1) (nat_to_bits sz b2)) % (2^sz.val), ♯⟩

def bitwise_or := @bitwise_op sz bor
def bitwise_and := @bitwise_op sz band
def bitwise_xor := @bitwise_op sz (λ b1 b2, ¬(b1 = b2))

def shl (b1 b2:bitvector sz): bitvector sz :=
  ⟨(b1 * (2^(if b2.val ≥ sz.val then sz.val else b2.val))) % 2^sz.val, ♯⟩
def shl_overflows (signed:bool) (b1 b2:bitvector sz) : bool :=
  if signed then
    let i1 := to_int b1, sft := b2.1 % sz, s := int.of_nat (2^(sz.val - 1)) in
    let v := i1 * int.of_nat (2^sft) in
    v < 0 - s ∨ s ≤ v
  else
    let i1 := b1.1, sft := b2.1 % sz, s := (2 ^ sz.val) in
    let v := i1 * (2^sft) in
    s ≤ v

def lshr (b1 b2:bitvector sz): bitvector sz :=
  ⟨(b1 / (2^(b2.val % sz))) % (2 ^ sz.val), ♯⟩
def ashr (b1 b2:bitvector sz): bitvector sz :=
  let n2  := b2.1 % sz,
      sgn := b1.1 / (2^(sz.val - 1)),
      mask := 2^sz.val - sgn * 2^(sz.val - n2) in
  ⟨((b1 / (2^(b2.val % sz.val))) + mask) % 2^sz.val, ♯⟩

def eq (b1 b2:bitvector sz) : bool :=
  b1 = b2
def ne (b1 b2:bitvector sz) : bool :=
  b1 ≠ b2
def sle (b1 b2:bitvector sz) : bool :=
  to_int b1 ≤ to_int b2
def slt (b1 b2:bitvector sz) : bool :=
  to_int b1 < to_int b2
def ule (b1 b2:bitvector sz) : bool :=
  b1.1 ≤ b2.1
def ult (b1 b2:bitvector sz) : bool :=
  b1.1 < b2.1

def zext (sz2:size) (b1:bitvector sz) : bitvector sz2 :=
  ⟨b1.1 % (2^sz2.val), ♯⟩
def sext (sz2:size) (b1:bitvector sz) : bitvector sz2 :=
  ⟨(of_int (sz.add sz2) (to_int b1)) % (2^sz2.val), ♯⟩
def trunc (sz2:size) (b1:bitvector sz) : bitvector sz2 :=
  ⟨b1.1 % (2^sz2.val), ♯⟩

end bitvector


instance bitvector_is_uint_like
: uint_like bitvector :=
⟨@bitvector.add, @bitvector.sub, @bitvector.mul,
  @bitvector.udiv, @bitvector.urem, @bitvector.sdiv, @bitvector.srem,
  @bitvector.bitwise_and, @bitvector.bitwise_or, @bitvector.bitwise_xor,
  @bitvector.shl, @bitvector.lshr, @bitvector.ashr,
  bitvector.zero, bitvector.all_one, bitvector.int_min,
  bitvector.of_int, @bitvector.zext, @bitvector.sext, @bitvector.trunc⟩

instance bool_bitvec_has_coe: has_coe bool (bitvector size.one) :=
⟨bitvector.of_bool⟩

@[reducible]
instance bitvector_has_comp
: has_comp bitvector bool :=
⟨@bitvector.eq, @bitvector.ne, @bitvector.sle, @bitvector.slt,
  @bitvector.ule, @bitvector.ult⟩

instance bitvector_has_overflow_check
: has_overflow_check bitvector bool :=
⟨@bitvector.add_overflows, @bitvector.sub_overflows,
 @bitvector.mul_overflows, @bitvector.shl_overflows⟩

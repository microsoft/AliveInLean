def size := { n:nat // 0 < n }

namespace size

instance size_to_nat: has_coe size nat :=
⟨λ s, s.1⟩

instance : has_to_string size :=
⟨λ s, to_string s.1⟩

@[pattern, reducible] def one : size := ⟨1, dec_trivial⟩

@[reducible] def add (sz1:size) (sz2:size):size :=
⟨sz1.1 + sz2.1, nat.lt_trans sz1.2 -- 0 < sz -> sz < sz+sz2 -> 0 < sz+sz2
    (nat.lt_add_of_pos_right sz2.2)⟩
instance : has_add size := ⟨add⟩

@[reducible] def incr (sz:size):size := sz.add size.one

def incr_nat (sz:nat):size := ⟨nat.succ sz, dec_trivial⟩

@[reducible] def sub (sz1:size) (sz2:size) (prf:sz1.1 > sz2.1):size :=
⟨sz1.1 - sz2.1, nat.sub_pos_of_lt prf⟩


theorem add_sub_eq (sz1 sz2:size) (prf:sz1.1 > sz2.1) :
  (sz2.add (sz1.sub sz2 prf)) = sz1 :=
begin
  apply subtype.eq, simp,
  rw nat.add_sub_of_le (nat.le_of_succ_le prf)
end

theorem add_sub_eq2 (sz1 sz2:size) (prf:(sz1.add sz2).val > sz2.val) :
  ((sz1.add sz2).sub sz2 prf) = sz1 :=
begin
  apply subtype.eq, simp, apply nat.add_sub_cancel
end

theorem add_gt (sz m:size):
  (sz.add m).val > sz.val :=
begin
  cases sz,
  cases m,
  simp, apply lt_add_of_pos_right, assumption
end

theorem add_gt2 (sz m:size):
  (sz.add m).val > m.val :=
begin
  cases sz,
  cases m,
  simp, rw nat.add_comm, apply lt_add_of_pos_right, assumption
end

theorem add_one_incr_eq (sz1:size) : 
  (sz1.incr) = (sz1.add size.one) :=
begin apply subtype.eq, simp end

end size

@[reducible] def within_signed_range (sz:size) (x:ℤ) : Prop :=
  (-int.of_nat (2 ^ (sz.val - 1)) ≤ x) ∧ (x < int.of_nat (2 ^ (sz.val - 1)))

def all_one_nat (sz:size) : ℕ := (2 ^ sz.val) - 1
def int_min_nat (sz:size) : ℕ := 2 ^ (sz.val - 1)

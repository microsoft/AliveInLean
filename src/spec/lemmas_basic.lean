universes u v
-- Basic
lemma prod_inj: ∀ {α:Type u} {β:Type v} (p q:α × β),
  p = q ↔ p.fst = q.fst ∧ p.snd = q.snd
:= begin
  intros,
  split,
  { intros H, rw H, split; refl },
  { intros H, cases p, cases q, simp at H,
    cases H with H1 H2, rw [H1, H2] }
end

-- Arithmetic operations

lemma nat.pow_mul_pow: ∀ (m n:ℕ),
  m * m^n = m^(n+1)
:= begin
  intros, apply nat.mul_comm
end

lemma nat.lt_pow2: ∀ (n:ℕ),
  n < 2^n
:= begin
  intros,
  induction n,
  { simp, constructor },
  {
    have n_ih := nat.succ_lt_succ n_ih,
    apply lt_of_lt_of_le,
    { apply n_ih },
    { unfold has_pow.pow, rw nat.pow, rw nat.mul_comm, rw nat.succ_mul,
      simp, rw ← nat.add_one,
      apply nat.add_le_add_left,
      apply nat.pos_pow_of_pos, constructor, constructor
    }
  }
end

lemma nat.mod_pow2: ∀ (x:ℕ),
  x % 2^x = x
:= begin
  intros, apply nat.mod_eq_of_lt, apply nat.lt_pow2
end

lemma neq_symm: ∀ {α:Type u} (x y:α),
  x ≠ y → y ≠ x
:= begin
  intros, intros H, rw H at a, apply a, refl
end

lemma nat.not_gt_not_eq_implies_lt: ∀ (x y:ℕ),
  ¬(x > y) → (x ≠ y) → x < y
:= begin
  intros x y H1 H2,
  have H3 := nat.lt_or_ge x y,
  apply or.resolve_right,
  apply H3,
  intros H0, apply H1, apply nat.lt_of_le_and_ne, apply H0, apply neq_symm, assumption
end

-- list

lemma list.foldl_unroll: ∀ {α:Type u} {β:Type v} {f:α → β → α} a (l:list β) x,
  list.foldl f a (l++[x]) = f (list.foldl f a l) x
:= begin
  intros,
  revert a,
  induction l,
  { simp },
  { intros, simp, rw l_ih }
end

lemma list.notmem_and {α:Type u} [decidable_eq α] : ∀ (l:list α) h a,
  (a ∉ h::l) ↔ (a ≠ h ∧ a ∉ l)
:= begin
  intros, 
  have HD:decidable (a ∈ l),
  { apply (list.decidable_mem a l)},
  simp, rw decidable.not_or_iff_and_not
end

lemma list.cases_back: ∀ {α:Type u} (l:list α),
  l = [] ∨ ∃ a l', l = l' ++ [a]
:= begin
  intros,
  induction l,
  { left, refl },
  {
    cases l_ih,
    {
      right,
      rw l_ih,
      apply exists.intro l_hd,
      apply exists.intro [], refl
    },
    {
      cases l_ih,
      cases l_ih_h,
      right,
      rw l_ih_h_h,
      apply exists.intro l_ih_w,
      apply exists.intro (l_hd :: l_ih_h_w),
      refl
    }
  }
end

lemma list.map_nil: ∀ {α:Type u} {β:Type v} (l:list α) (f:α → β)
  (H:list.map f l = []), l = []
:= begin
  intros,
  induction l,
  simp, simp at H, cases H
end

lemma list.map_eq: ∀ {α:Type u} {β:Type v} (l:list α) (f g:α → β)
  (H:∀ x, f x = g x),
  l.map f = l.map g
:= begin
  intros, induction l; simp [*]
end

lemma list.foldr_inv: ∀ {α:Type u} {β:Type v} (la:list α) (b:β) (f:α → β → β)
    (P:β → Prop)
    (HINV:∀ b', P b' → ∀ a', P (f a' b'))
    (H0:P b),
  P (list.foldr f b la)
:= begin
  intros,
  induction la,
  { simp, assumption },
  { simp, apply HINV, assumption }
end

lemma list.foldr_eq: ∀ {α:Type u} {β:Type v} (la1 la2:list α)
    (b1 b2:β) (f1 f2:α → β → β)
    (HF: ∀ a b, f1 a b = f2 a b)
    (HLA:la1 = la2)
    (HB: b1 = b2),
  list.foldr f1 b1 la1 = list.foldr f2 b2 la2
:= begin
  intros,
  revert la1,
  induction la2,
  { intros, subst HLA, simp, assumption },
  { intros,
    subst HLA,
    simp,
    rw la2_ih,
    apply HF, refl
  }
end

lemma list.append_eq: ∀ {α:Type u} {l l21 l22:list α},
  l ++ l21 = l ++ l22 → l21 = l22
:= begin
  intros,
  induction l, simp at a, assumption,
  apply l_ih, simp at a, assumption
end

lemma list.append_nil_eq: ∀ {α:Type u} {l l2:list α},
  l = l2 ++ l → l2 = []
:= begin
  intros, induction l with h t, simp at a, rw a,
  cases l2, refl,
  have a' : (h :: t).length = (l2_hd :: l2_tl ++ h :: t).length, rw ← a,
  simp at a',
  have a' := nat.add_left_cancel a',
  rw ← nat.add_assoc at a',
  rw nat.add_comm 1 at a',
  rw nat.add_assoc at a',
  rw ← nat.add_zero (list.length t) at a',
  have a' := nat.add_left_cancel a',
  rw nat.one_add at a', cases a'
end

lemma list.append_eq2: ∀ {α:Type u} {l l1 l2:list α},
  l1 ++ l = l2 ++ l → l1 = l2
:= begin
  intros,
  revert l2,
  induction l1, intros, simp at a, rw list.append_nil_eq a,
  intros, cases l2,
  rw list.nil_append at a, have a' := list.append_nil_eq (eq.symm a), assumption,
  injection a, rw h_1, rw l1_ih, apply h_2
end


inductive list.unique {α:Type u}: list α → Prop
| nil: list.unique []
| cons: ∀ a l (H:list.unique l) (H2:a ∉ l), list.unique (a::l)


lemma list.not_mem_append: ∀ {α:Type u} {a} {l1 l2:list α}
  (H1: a ∉ l1) (H2: a ∉ l2), a ∉ (l1 ++ l2)
:= begin
  intros, intros H0, rw list.mem_append at H0,
  cases H0, apply H1, assumption, apply H2, assumption
end

-- if two lists are different, appended lists are always different
lemma list.append_ne {α:Type u}:
  ∀ {s1 s2:list α} {a1 a2:α} (H:a1 ≠ a2),
  s1 ++ [a1] ≠ s2 ++ [a2]
:= begin
  intros, revert s2,
  induction s1,
  {
    intros, cases s2, simp, assumption,
    simp, intros H, cases H, cases s2_tl,
    simp at H_right, assumption, cases H_right
  },
  {
    intros, intros H, cases s2, simp at H,
    cases H, cases s1_tl, simp at H_right, assumption,
    simp at H_right, assumption,
    apply s1_ih, simp at H, cases H, assumption
  }
end

-- strings

def string.reverse (s:string):string := s.to_list.reverse.as_string

lemma string.append_to_list: ∀ {s1 s2:string},
  (s1 ++ s2).to_list = s1.to_list ++ s2.to_list
:= begin
  intros,
  cases s1, cases s2,
  unfold string.to_list,
  refl
end

lemma string.eq_list: ∀ {s1 s2:string},
  s1 = s2 ↔ s1.to_list = s2.to_list
:= begin
  intros,
  split,
  intros,
  cases s1, cases s2,
  injection a,
  intros, cases s1, cases s2, unfold string.to_list at a, rw a
end

lemma string.eq_suffix: ∀ {s1 s2 suffix:string}
  (H:s1 ++ suffix = s2 ++ suffix), s1 = s2
:= begin
  intros,
  rw string.eq_list at H,
  rw string.append_to_list at H,
  rw string.append_to_list at H,
  have H := list.append_eq2 H,
  rw string.eq_list,
  assumption
end

lemma string.eq_prefix: ∀ {s1 s2 pref:string}
  (H:pref++s1 = pref++s2), s1 = s2
:= begin
  intros,
  rw string.eq_list at H,
  rw string.append_to_list at H,
  rw string.append_to_list at H,
  have H := list.append_eq H,
  rw string.eq_list,
  assumption
end

lemma slist_prefix_notin: ∀ {l: list string} {a} (pref: string)
  (H:a ∉ l), pref ++ a ∉ l.map (λs, pref ++ s)
:= begin
  intros,
  intros H',
  apply H, clear H,
  induction l with h t, simp at H', cases H',
  simp at *,
  cases H', left, apply string.eq_prefix, assumption,
  right, apply l_ih, assumption
end

-- Just a special case - if first characters of two prefixes are
-- different, ∉ holds.
lemma slist_prefix_notin2: ∀ {l: list string} {a}
    (pfx1 pfx2: string) {pfx1_t pfx2_t: list char} (pfx1_h pfx2_h : char)
    (H:a ∉ l) (HNE:pfx1_h ≠ pfx2_h)
    (H1:pfx1 = (pfx1_h::pfx1_t).as_string)
    (H1:pfx2 = (pfx2_h::pfx2_t).as_string),
  pfx1 ++ a ∉ l.map (λs, pfx2 ++ s)
:= begin
  intros,
  induction l with h t,
  { simp },
  rw list.map,
  intros H0, apply l_ih,
  { intros H', apply H, simp, right, assumption },
  simp at H0,
  cases H0,
  {
    rw string.eq_list at H0,
    rw string.append_to_list at H0,
    rw string.append_to_list at H0,
    rw [H1, H1_1] at H0,
    unfold list.as_string at H0,
    unfold string.to_list at H0,
    simp at H0, cases H0, exfalso, apply HNE, assumption
  }, apply H0
end

lemma slist_prefix_unique: ∀ (l: list string) (pref: string)
  (H:list.unique l), list.unique (l.map (λs, pref ++ s))
:= begin
  intros,
  induction l with h t,
  { apply H },
  {
    cases H, have H := l_ih H_H,
    apply list.unique.cons, assumption,
    simp, apply slist_prefix_notin, assumption
  }
end
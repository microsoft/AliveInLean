import ..smtexpr
import ..bitvector
import ..irsem
import .spec
import .lemmas
import .irstate
import smt2.syntax
import system.io
import init.meta.tactic
import init.meta.interactive

namespace spec

open irsem

def env.added2 (η:freevar.env) (n1 n2:string) (η':freevar.env):=
  (∀ n, n ∉ η → n ≠ n1 ∧ n ≠ n2 → n ∉ η') ∧
  (∀ n, n ∈ η ∨ n = n1 ∨ n = n2 → n ∈ η')

def env.has_only (η:freevar.env) (names:list string) :=
  ∀ name, name ∈ names ↔ name ∈ η

universes u v
@[reducible]
def apply {α:Type u} (f:α → α) : option α → option α
| (some x) := some (f x)
| none := none

lemma apply_none: ∀ {α:Type u} (f:α → α) o,
  apply f o = none ↔ o = none
:= begin
  intros,
  split,
  { intros H, cases o, refl, unfold apply at H, cases H },
  { intros H, rw H }
end

lemma apply_some: ∀ {α:Type u} {f:α → α} {o} {v}
  (H:apply f o = some v), ∃ v', o = some v'
:= begin
  intros,
  cases o with v0,
  { unfold apply at H, cases H },
  { unfold apply at H, apply exists.intro v0, refl }
end

notation η `⟦` s `⟧'` := apply (freevar.env.replace η) s
notation η `⟦` s `⟧'` := apply (freevar.env.replace_valty η) s
notation η `⟦` s `⟧'` := apply (freevar.env.replace_sbv η) s
notation η `⟦` s `⟧'` := apply (freevar.env.replace_sb η) s


-- Induction principles for sbool & sbitvec which are mutually defined
section
@[reducible]
parameters (P:sbool → Prop) (P':Π {sz:size}, sbitvec sz → Prop)
  (Hbtt: P sbool.tt) (Hbff: P sbool.ff) (Hbvar: ∀ s, P (sbool.var s))
  (Hband: ∀ b1 b2, P b1 → P b2 → P (sbool.and b1 b2))
  (Hbor: ∀ b1 b2, P b1 → P b2 → P (sbool.or b1 b2))
  (Hbxor: ∀ b1 b2, P b1 → P b2 → P (sbool.xor b1 b2))
  (Hbeqb: ∀ b1 b2, P b1 → P b2 → P (sbool.eqb b1 b2))
  (Hbneb: ∀ b1 b2, P b1 → P b2 → P (sbool.neb b1 b2))
  (Hbite: ∀ b1 b2 b3, P b1 → P b2 → P b3 → P (sbool.ite b1 b2 b3))
  (Hbnot: ∀ b, P b → P (sbool.not b))
  (Hbeqbv: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P (sbool.eqbv v1 v2))
  (Hbnebv: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P (sbool.nebv v1 v2))
  (Hbsle: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P (sbool.sle v1 v2))
  (Hbslt: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P (sbool.slt v1 v2))
  (Hbule: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P (sbool.ule v1 v2))
  (Hbult: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P (sbool.ult v1 v2))
  (Hvconst: ∀ sz n, P' (sbitvec.const sz n))
  (Hvvar: ∀ sz n, P' (sbitvec.var sz n))
  (Hvadd: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.add v1 v2))
  (Hvsub: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.sub v1 v2))
  (Hvmul: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.mul v1 v2))
  (Hvudiv: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.udiv v1 v2))
  (Hvurem: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.urem v1 v2))
  (Hvsdiv: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.sdiv v1 v2))
  (Hvsrem: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.srem v1 v2))
  (Hvand: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.and v1 v2))
  (Hvor: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.or v1 v2))
  (Hvxor: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.xor v1 v2))
  (Hvshl: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.shl v1 v2))
  (Hvlshr: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.lshr v1 v2))
  (Hvashr: ∀ {sz} (v1 v2:sbitvec sz), P' v1 → P' v2 → P' (sbitvec.ashr v1 v2))
  (Hvzext: ∀ {sz} (v:sbitvec sz) sz', P' v → P' (sbitvec.zext sz' v))
  (Hvsext:∀ {sz} (v:sbitvec sz) sz', P' v → P' (sbitvec.sext sz' v))
  (Hvtrunc: ∀ {sz} (v:sbitvec sz) sz', P' v → P' (sbitvec.trunc sz' v))
  (Hvextract: ∀ {sz sz':size} (v:sbitvec sz) highbit lowbit
      (H:sz'.val = highbit - lowbit + 1),
      P' v → P' (sbitvec.extract highbit lowbit H v))
  (Hvite: ∀ {sz} (b:sbool) (v1 v2:sbitvec sz), P b → P' v1 → P' v2 →
      P' (sbitvec.ite b v1 v2))

@[reducible]
mutual def sbool.induction, sbitvec.induction
with sbool.induction : ∀ b, P b
| sbool.tt := Hbtt
| sbool.ff := Hbff
| (sbool.var b) := Hbvar b
| (sbool.and b1 b2) := Hband b1 b2 (sbool.induction b1) (sbool.induction b2)
| (sbool.or b1 b2) := Hbor b1 b2 (sbool.induction b1) (sbool.induction b2)
| (sbool.xor b1 b2) := Hbxor b1 b2 (sbool.induction b1) (sbool.induction b2)
| (sbool.eqb b1 b2) := Hbeqb b1 b2 (sbool.induction b1) (sbool.induction b2)
| (sbool.neb b1 b2) := Hbneb b1 b2 (sbool.induction b1) (sbool.induction b2)
| (sbool.ite b1 b2 b3) := Hbite b1 b2 b3 (sbool.induction b1) (sbool.induction b2) (sbool.induction b3)
| (sbool.not b) := Hbnot b (sbool.induction b)
| (@sbool.eqbv sz v1 v2) :=
    have 0 < sbitvec.sizeof sz v1, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz v2, by apply sbitvec.decr_sbitvec,
    Hbeqbv v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| (@sbool.nebv sz v1 v2) :=
    have 0 < sbitvec.sizeof sz v1, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz v2, by apply sbitvec.decr_sbitvec,
    Hbnebv v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| (@sbool.sle sz v1 v2) := 
    have 0 < sbitvec.sizeof sz v1, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz v2, by apply sbitvec.decr_sbitvec,
    Hbsle v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| (@sbool.slt sz v1 v2) := 
    have 0 < sbitvec.sizeof sz v1, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz v2, by apply sbitvec.decr_sbitvec,
    Hbslt v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| (@sbool.ule sz v1 v2) := 
    have 0 < sbitvec.sizeof sz v1, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz v2, by apply sbitvec.decr_sbitvec,
    Hbule v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| (@sbool.ult sz v1 v2) := 
    have 0 < sbitvec.sizeof sz v1, by apply sbitvec.decr_sbitvec,
    have 0 < sbitvec.sizeof sz v2, by apply sbitvec.decr_sbitvec,
    Hbult v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
with sbitvec.induction: ∀ {sz:size} (v:sbitvec sz), P' v
| _ (sbitvec.const sz n) := Hvconst sz n
| _ (sbitvec.var sz n) := Hvvar sz n
| _ (sbitvec.add v1 v2) := Hvadd v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.sub v1 v2) := Hvsub v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.mul v1 v2) := Hvmul v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.udiv v1 v2) := Hvudiv v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.urem v1 v2) := Hvurem v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.sdiv v1 v2) := Hvsdiv v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.srem v1 v2) := Hvsrem v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.and v1 v2) := Hvand v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.or v1 v2) := Hvor v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.xor v1 v2) := Hvxor v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.shl v1 v2) := Hvshl v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.lshr v1 v2) := Hvlshr v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.ashr v1 v2) := Hvashr v1 v2 (sbitvec.induction v1) (sbitvec.induction v2)
| _ (sbitvec.zext sz' v) := Hvzext v sz' (sbitvec.induction v)
| _ (sbitvec.sext sz' v) := Hvsext v sz' (sbitvec.induction v)
| _ (sbitvec.trunc sz' v) := Hvtrunc v sz' (sbitvec.induction v)
| _ (sbitvec.extract h l H v) := Hvextract v h l H (sbitvec.induction v)
| _ (sbitvec.ite b v1 v2) := Hvite b v1 v2 (sbool.induction b)
      (sbitvec.induction v1) (sbitvec.induction v2)

end


lemma env.replace_sb_and0: ∀ (b1 b2:sbool) (η:freevar.env),
  η⟦sbool.and b1 b2⟧ = sbool.and (η⟦b1⟧) (η⟦b2⟧)
:= begin intros, unfold freevar.env.replace_sb end
lemma env.replace_sb_and: ∀ (b1 b2:sbool) (η:freevar.env),
  η⟦b1 & b2⟧ = η⟦b1⟧ & η⟦b2⟧
:= begin intros, apply env.replace_sb_and0 end

lemma env.replace_sb_or0: ∀ (b1 b2:sbool) (η:freevar.env),
  η⟦sbool.or b1 b2⟧ = sbool.or (η⟦b1⟧) (η⟦b2⟧)
:= begin intros, unfold freevar.env.replace_sb end
lemma env.replace_sb_or: ∀ (b1 b2:sbool) (η:freevar.env),
  η⟦b1 |b b2⟧ = η⟦b1⟧ |b η⟦b2⟧
:= begin intros, apply env.replace_sb_or0 end

lemma env.replace_sb_not0: ∀ (b:sbool) (η:freevar.env),
  η⟦sbool.not b⟧ = sbool.not (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sb end
lemma env.replace_sb_not: ∀ (b:sbool) (η:freevar.env),
  η⟦~ b⟧ = ~ η⟦b⟧
:= begin intros, apply env.replace_sb_not0 end

lemma env.replace_sb_eqbv: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbool.eqbv a b⟧ = sbool.eqbv (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sb end

lemma env.replace_sb_nebv: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbool.nebv a b⟧ = sbool.nebv (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sb end

lemma env.replace_sb_sle: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbool.sle a b⟧ = sbool.sle (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sb end

lemma env.replace_sb_slt: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbool.slt a b⟧ = sbool.slt (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sb end

lemma env.replace_sb_ule: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbool.ule a b⟧ = sbool.ule (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sb end

lemma env.replace_sb_ult: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbool.ult a b⟧ = sbool.ult (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sb end

lemma env.replace_sb_ite: ∀ (c:sbool) (a b:sbool) (η:freevar.env),
  η⟦sbool.ite c a b⟧ = sbool.ite (η⟦c⟧) (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sb end

lemma env.replace_b2p: ∀ (b:sbool) (η:freevar.env),
  η⟦b2p irsem_smt b⟧ = b2p irsem_smt (η⟦b⟧)
:= begin
  intros,
  unfold b2p,
  unfold has_ite.ite,
  unfold freevar.env.replace_sb,
  refl
end

lemma env.replace_sb_of_bool: ∀ (a:bool) (η:freevar.env),
  η⟦sbool.of_bool a⟧ = sbool.of_bool a
:= begin
  intros, cases a; refl
end

lemma env.replace_eq2p: ∀ {sz:size} (v1:sbitvec sz) (v2:sbitvec sz) (η:freevar.env),
  η⟦irsem.eq2p irsem_smt v1 v2⟧ = (irsem.eq2p irsem_smt (η⟦v1⟧) (η⟦v2⟧))
:= begin
  intros,
  unfold eq2p,
  unfold has_ne.ne,
  unfold has_comp.ne,
  have HNE: sbool.nebv (η⟦v1⟧) (η⟦v2⟧) = η⟦sbool.nebv v1 v2⟧,
  {
    unfold freevar.env.replace_sb
  },
  rw HNE,
  apply env.replace_b2p,
end

lemma env.replace_neq2p: ∀ {sz:size} (v1:sbitvec sz) (v2:sbitvec sz) (η:freevar.env),
  η⟦irsem.neq2p irsem_smt v1 v2⟧ = (irsem.neq2p irsem_smt (η⟦v1⟧) (η⟦v2⟧))
:= begin
  intros,
  unfold neq2p,
  unfold has_eq.eq,
  unfold has_comp.eq,
  have HNE: sbool.eqbv (η⟦v1⟧) (η⟦v2⟧) = η⟦sbool.eqbv v1 v2⟧,
  {
    unfold freevar.env.replace_sb
  },
  rw HNE,
  apply env.replace_b2p,
end

lemma env.replace_eq2p': ∀ {sz:size} (v1:sbitvec sz) (v2:sbitvec sz) (η:freevar.env)
    (H:v2 = η⟦v2⟧),
  (irsem.eq2p irsem_smt (η⟦v1⟧) v2) = η⟦irsem.eq2p irsem_smt v1 v2⟧
:= begin
  intros,
  have H0: irsem.eq2p irsem_smt (η⟦v1⟧) v2 = irsem.eq2p irsem_smt (η⟦v1⟧) (η⟦v2⟧),
  { rw ← H },
  rw H0,
  rw ← env.replace_eq2p
end

-- replace_sbv

lemma env.replace_sbv_add: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.add a b⟧ = sbitvec.add (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_sub: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.sub a b⟧ = sbitvec.sub (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_mul: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.mul a b⟧ = sbitvec.mul (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_udiv: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.udiv a b⟧ = sbitvec.udiv (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_urem: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.urem a b⟧ = sbitvec.urem (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_sdiv: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.sdiv a b⟧ = sbitvec.sdiv (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_srem: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.srem a b⟧ = sbitvec.srem (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_shl: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.shl a b⟧ = sbitvec.shl (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_lshr: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.lshr a b⟧ = sbitvec.lshr (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_ashr: ∀ {sz:size} (a b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.ashr a b⟧ = sbitvec.ashr (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_mk_zext: ∀ {sz sz2:size} (a:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.mk_zext sz2 a⟧ = sbitvec.mk_zext sz2 (η⟦a⟧)
:= begin intros, unfold sbitvec.mk_zext, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_mk_sext: ∀ {sz sz2:size} (a:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.mk_sext sz2 a⟧ = sbitvec.mk_sext sz2 (η⟦a⟧)
:= begin intros, unfold sbitvec.mk_sext, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_trunc: ∀ {sz sz':size} (b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.trunc sz' b⟧ = sbitvec.trunc sz' (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_zext: ∀ {sz sz':size} (b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.zext sz' b⟧ = sbitvec.zext sz' (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_sext: ∀ {sz sz':size} (b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.sext sz' b⟧ = sbitvec.sext sz' (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_extract: ∀ {sz sz':size} (b:sbitvec sz) (η:freevar.env) h l 
    (H:sz'.val = h - l + 1),
  η⟦sbitvec.extract h l H b⟧ = sbitvec.extract h l H (η⟦b⟧)
:= begin
  intros,
  unfold freevar.env.replace_sbv
end

lemma env.replace_sbv_ite: ∀ {sz:size} (c:sbool) (a b:sbitvec sz) (η:freevar.env),
  η⟦sbitvec.ite c a b⟧ = sbitvec.ite (η⟦c⟧) (η⟦a⟧) (η⟦b⟧)
:= begin intros, unfold freevar.env.replace_sbv end

lemma env.replace_sbv_of_int: ∀ sz z (η:freevar.env),
  η⟦sbitvec.of_int sz z⟧ = sbitvec.of_int sz z
:= begin
  intros,
  cases sz,
  cases z;
  {
    unfold sbitvec.of_int,
    unfold freevar.env.replace_sbv
  }
end

lemma env.replace_sbv_of_bool: ∀ (a:sbool) (η:freevar.env),
  η⟦sbitvec.of_bool a⟧ = sbitvec.of_bool (η⟦a⟧)
:= begin
  intros, unfold sbitvec.of_bool, rw env.replace_sbv_ite,
  unfold sbitvec.zero, unfold sbitvec.one,
  rw env.replace_sbv_of_int, rw env.replace_sbv_of_int
end



lemma env.replace_idemp :
  (∀ (η:freevar.env) (b:sbool), η⟦η⟦b⟧⟧ = η⟦b⟧) ∧
  (∀ {sz:size} (η:freevar.env) (b:sbitvec sz), η⟦η⟦b⟧⟧ = η⟦b⟧) 
:= begin
  split; intros; revert b,
  apply (sbool.induction (λ b, η⟦η⟦b⟧⟧ = η⟦b⟧)
                        (λ {sz:size} (v:sbitvec sz), η⟦η⟦v⟧⟧ = η⟦v⟧)),
  any_goals  {
    apply (sbitvec.induction (λ b, η⟦η⟦b⟧⟧ = η⟦b⟧)
                          (λ {sz:size} (v:sbitvec sz), η⟦η⟦v⟧⟧ = η⟦v⟧))
  },
  any_goals
  { refl },
  -- sbool
  any_goals {
    intros b1 b2 H1 H2,
    unfold freevar.env.replace_sb, rw [H1, H2], done
  },
  any_goals {
    intros,
    unfold freevar.env.replace_sb,
    generalize Hb': η.b s = b',
    cases b',
    { unfold freevar.env.replace_sb._match_1,
      unfold freevar.env.replace_sb,
      rw Hb', refl
    },
    { unfold freevar.env.replace_sb._match_1,
      cases b'; refl
    }
  },
  any_goals { intros b1 b2 b3 H1 H2 H3,
    unfold freevar.env.replace_sb, rw [H1, H2, H3], done
  },
  any_goals { intros b H,
    unfold freevar.env.replace_sb, rw H, done
  },
  any_goals { intros sz v1 v2 H1 H2,
    unfold freevar.env.replace_sb, rw H1, rw H2, done
  },
  -- sbitvec
  any_goals
  { intros, unfold freevar.env.replace_sbv, done },
  any_goals {
    intros sz v1 v2 H1 H2,
    unfold freevar.env.replace_sbv, rw [H1, H2], done
  },
  any_goals {
    intros,
    unfold freevar.env.replace_sbv,
    generalize Hb': η.bv n = b',
    cases b'; unfold freevar.env.replace_sbv._match_1,
    { unfold freevar.env.replace_sbv,
      rw Hb', refl
    },
    { rw env.replace_sbv_of_int }, done
  },
  any_goals {
    intros sz v' sz' H,
    unfold freevar.env.replace_sbv, rw H, done
  },
  any_goals {
    intros sz sz' v highbit lowbit H H',
    unfold freevar.env.replace_sbv,
    rw H', done
  },
  any_goals {
    intros sz b v1 v2 H H1 H2,
    unfold freevar.env.replace_sbv,
    rw [H, H1, H2]
  }
end

lemma env.replace_sb_idemp: ∀ (η:freevar.env) (b:sbool), η⟦η⟦b⟧⟧ = η⟦b⟧
:= begin
  apply (and.elim_left env.replace_idemp)
end

lemma env.replace_sbv_idemp: ∀ {sz} (η:freevar.env) (b:sbitvec sz), η⟦η⟦b⟧⟧ = η⟦b⟧
:= begin
  intros,
  apply (and.elim_right env.replace_idemp)
end

lemma env.empty_replace: (∀ (b:sbool), freevar.env.empty⟦b⟧ = b) ∧
  (∀ {sz} (b:sbitvec sz), freevar.env.empty⟦b⟧ = b)
:= begin
  intros,
  split; intros; revert b,
  apply (sbool.induction (λ b, freevar.env.empty⟦b⟧ = b)
              (λ {sz:size} (v:sbitvec sz), freevar.env.empty⟦v⟧ = v)),
  any_goals {
    apply (sbitvec.induction (λ b, freevar.env.empty⟦b⟧ = b)
              (λ {sz:size} (v:sbitvec sz), freevar.env.empty⟦v⟧ = v)),
  },
  any_goals { refl },
  any_goals {
    intros,
    unfold freevar.env.replace_sb,
    unfold freevar.env.empty,
    simp,
    unfold freevar.env.replace_sb._match_1
  },
  any_goals {
    intros b H, unfold freevar.env.replace_sb, rw H, done
  },
  any_goals {
    intros b1 b2 H1 H2, unfold freevar.env.replace_sb, rw [H1, H2], done
  },
  any_goals {
    intros b b1 b2 H H1 H2, unfold freevar.env.replace_sb, rw [H, H1, H2], done
  },
  any_goals {
    intros sz b1 b2 H1 H2, unfold freevar.env.replace_sb, rw [H1, H2], done
  },
  -- sbitvec
  any_goals
  { intros, unfold freevar.env.replace_sbv, done },
  any_goals {
    intros sz v1 v2 H1 H2,
    unfold freevar.env.replace_sbv, rw [H1, H2], done
  },
  any_goals {
    intros,
    unfold freevar.env.replace_sbv,
    unfold freevar.env.empty,
    simp,
    unfold freevar.env.replace_sbv._match_1
  },
  any_goals {
    intros sz v' sz' H,
    unfold freevar.env.replace_sbv, rw H, done
  },
  any_goals {
    intros sz sz' v highbit lowbit H H',
    unfold freevar.env.replace_sbv,
    rw H', done
  },
  any_goals {
    intros sz b v1 v2 H H1 H2,
    unfold freevar.env.replace_sbv,
    rw [H, H1, H2]
  }
end

lemma env.empty_replace_sb: ∀ (b:sbool), freevar.env.empty⟦b⟧ = b
:= begin
  apply (and.elim_left env.empty_replace)
end

lemma env.empty_replace_sbv {sz:size} : ∀ (b:sbitvec sz), freevar.env.empty⟦b⟧ = b
:= begin
  apply (and.elim_right env.empty_replace)
end

lemma env.replace_sbv_cast: ∀ {sz sz':size} {H:sz = sz'} {H':sbitvec sz = sbitvec sz'}
    (b:sbitvec sz) (η:freevar.env),
  η⟦cast H' b⟧ = cast H' (η⟦b⟧)
:= begin
  intros,
  induction H,
  unfold cast
end

lemma env.replace_sb_overflowchk_add: ∀
    {sz1:size} (sz2:size) (v1 v2:sbitvec sz1) nsw (η:freevar.env),
  η⟦sbitvec.overflow_chk @sbitvec.add sz2 nsw v1 v2⟧ =
    sbitvec.overflow_chk @sbitvec.add sz2 nsw (η⟦v1⟧) (η⟦v2⟧)
:= begin
  intros, unfold sbitvec.overflow_chk,
  cases nsw; simp; unfold freevar.env.replace_sb,
  {
    rw env.replace_sbv_extract,
    rw env.replace_sbv_add,
    repeat { rw env.replace_sbv_mk_zext },
    unfold sbitvec.zero, rw env.replace_sbv_of_int
  },
  {
    rw env.replace_sbv_add,
    repeat { rw env.replace_sbv_mk_sext },
    rw env.replace_sbv_add
  }
end

lemma env.replace_sb_overflowchk_sub: ∀
    {sz1:size} (sz2:size) (v1 v2:sbitvec sz1) nsw (η:freevar.env),
  η⟦sbitvec.overflow_chk @sbitvec.sub sz2 nsw v1 v2⟧ =
    sbitvec.overflow_chk @sbitvec.sub sz2 nsw (η⟦v1⟧) (η⟦v2⟧)
:= begin
  intros, unfold sbitvec.overflow_chk,
  cases nsw; simp; unfold freevar.env.replace_sb,
  {
    rw env.replace_sbv_extract,
    rw env.replace_sbv_sub,
    repeat { rw env.replace_sbv_mk_zext },
    unfold sbitvec.zero, rw env.replace_sbv_of_int
  },
  {
    rw env.replace_sbv_sub,
    repeat { rw env.replace_sbv_mk_sext },
    rw env.replace_sbv_sub
  }
end

lemma env.replace_sb_overflowchk_mul: ∀
    {sz1:size} (sz2:size) (v1 v2:sbitvec sz1) nsw (η:freevar.env),
  η⟦sbitvec.overflow_chk @sbitvec.mul sz2 nsw v1 v2⟧ =
    sbitvec.overflow_chk @sbitvec.mul sz2 nsw (η⟦v1⟧) (η⟦v2⟧)
:= begin
  intros, unfold sbitvec.overflow_chk,
  cases nsw; simp; unfold freevar.env.replace_sb,
  {
    rw env.replace_sbv_extract,
    rw env.replace_sbv_mul,
    repeat { rw env.replace_sbv_mk_zext },
    unfold sbitvec.zero, rw env.replace_sbv_of_int
  },
  {
    rw env.replace_sbv_mul,
    repeat { rw env.replace_sbv_mk_sext },
    rw env.replace_sbv_mul
  }
end

lemma env.replace_sb_overflowchk_shl: ∀
    {sz1:size} (sz2:size) (v1 v2:sbitvec sz1) nsw (η:freevar.env),
  η⟦sbitvec.shl_overflow_chk sz2 nsw v1 v2⟧ =
    sbitvec.shl_overflow_chk sz2 nsw (η⟦v1⟧) (η⟦v2⟧)
:= begin
  intros, unfold sbitvec.shl_overflow_chk,
  unfold sbitvec.overflow_chk,
  cases nsw; simp; unfold freevar.env.replace_sb,
  {
    rw env.replace_sbv_extract,
    rw env.replace_sbv_shl,
    repeat { rw env.replace_sbv_mk_zext },
    unfold sbitvec.zero, rw env.replace_sbv_of_int,
    rw env.replace_sbv_urem, rw env.replace_sbv_of_int
  },
  {
    rw env.replace_sbv_shl,
    repeat { rw env.replace_sbv_mk_sext },
    rw env.replace_sbv_shl,
    rw env.replace_sbv_urem, rw env.replace_sbv_of_int
  }
end

-- irstate

lemma getreg_replace_none: ∀ ss ss' (η:freevar.env) (name name':string)
    (H:irstate.getreg irsem_smt ss name = none)
    (H':ss' = η⟦ss⟧),
  irstate.getreg irsem_smt ss' name = none
:= begin
  intros,
  unfold freevar.env.replace at H',
  rw H',
  rw ← irstate.getreg_apply_none_smt,
  assumption
end

lemma getreg_replace_none_inv: ∀ ss ss' (η:freevar.env) (name name':string)
    (H:irstate.getreg irsem_smt ss' name = none)
    (H':ss' = η⟦ss⟧),
  irstate.getreg irsem_smt ss name = none
:= begin
  intros,
  unfold freevar.env.replace at H',
  rw H' at H,
  rw irstate.getreg_apply_none_smt,
  assumption
end

lemma getreg_replace: ∀ {ss:irstate_smt} {name:string} {η:freevar.env} {ov}
    (HV:irstate.getreg irsem_smt ss name = ov),
  irstate.getreg irsem_smt (η⟦ss⟧) name = η⟦ov⟧'
:= begin
  intros,
  revert ov,
  unfold irstate.getreg at *,
  unfold freevar.env.replace at *,
  unfold irstate.apply_to_values at *,
  cases ss with ss_ub ss_rf,
  apply regfile.induction ss_rf,
  {
    intros ov H,
    unfold irstate.setub, simp at *,
    rw regfile.empty_apply_empty,
    rw regfile.empty_get_none at *, rw ← H
  },
  {
    intros rf Hind n v ov H,
    unfold irstate.setub, simp at *,
    rw regfile.apply_update_comm,
    have HNAME: decidable (n = name), apply_instance,
    cases HNAME,
    {
      rw regfile.update_get_nomatch,
      apply Hind,
      { rw regfile.update_get_nomatch at H, apply H,
        apply neq_symm, assumption },
      { apply neq_symm, assumption }
    },
    {
      rw regfile.update_get_match,
      rw regfile.update_get_match at H,
      rw ← H, rw HNAME, rw HNAME
    }
  }
end

lemma replace_updatereg: ∀ (ss:irstate_smt) (name:string)
    (η:freevar.env) v,
  η⟦irstate.updatereg irsem_smt ss name v⟧ =
    irstate.updatereg irsem_smt (η⟦ss⟧) name (η⟦v⟧)
:= begin
  intros,
  unfold irstate.updatereg,
  unfold freevar.env.replace,
  unfold irstate.apply_to_values,
  congr
end

lemma replace_updateub: ∀ (ss:irstate_smt) (η:freevar.env) ub,
  η⟦irstate.updateub irsem_smt ss ub⟧ =
    irstate.updateub irsem_smt (η⟦ss⟧) (η⟦ub⟧)
:= begin
  intros,
  unfold irstate.updateub,
  unfold freevar.env.replace,
  unfold irstate.apply_to_values,
  unfold irstate.setub,
  unfold irstate.getub,
  simp,
  congr, rw env.replace_sb_and
end

lemma replace_getub: ∀ (ss:irstate_smt) (η:freevar.env),
  η⟦irstate.getub irsem_smt ss⟧ =
    irstate.getub irsem_smt (η⟦ss⟧)
:= begin
  intros,
  unfold irstate.getub,
  cases ss, refl
end

lemma empty_replace_st: ∀ (ss:irstate_smt),
  freevar.env.empty⟦ss⟧ = ss
:= begin
  intros,
  unfold freevar.env.replace,
  cases ss,
  unfold irstate.apply_to_values,
  unfold irstate.setub,
  unfold irstate.getub,
  simp,
  rw prod_inj,
  split,
  { rw env.empty_replace_sb },
  {
    simp,
    revert ss_snd,
    apply regfile.induction,
    { rw regfile.empty_apply_empty },
    {
      intros rf H,
      intros,
      rw regfile.apply_update_comm,
      congr, assumption, cases v,
      unfold freevar.env.replace_valty,
      congr, rw env.empty_replace_sbv, rw env.empty_replace_sb
    }
  }
end

-- ∉

lemma env.not_in_split: ∀ (η:freevar.env) n,
  n ∉ η ↔ η.b n = none ∧ η.bv n = none
:= begin
  intros,
  split; intros H,
  {
    unfold has_mem.mem at H,
    rw decidable.not_or_iff_and_not at H,
    cases H,
    rw ne.def at H_left,
    rw ne.def at H_right,
    rw decidable.not_not_iff at H_left,
    rw decidable.not_not_iff at H_right,
    split; assumption
  },
  {
    unfold has_mem.mem,
    rw decidable.not_or_iff_and_not,
    cases H,
    rw ne.def,
    rw ne.def,
    rw decidable.not_not_iff,
    rw decidable.not_not_iff,
    split; assumption
  }
end

lemma env.in_not_in: ∀ n (η:freevar.env), n ∉ η ∨ n ∈ η
:= begin
  intros,
  rw env.not_in_split,
  unfold has_mem.mem,
  generalize Hb: η.b n = b',
  generalize Hb: η.bv n = bv',
  cases b'; cases bv',
  {
    left, split; refl 
  },
  { right, right, intros H, cases H },
  { right, left, intros H, cases H },
  { right, left, intros H, cases H },
end

lemma env.not_in_add_bv: ∀ (η:freevar.env) n1 n2 z
    (HNEQ:n1 ≠ n2)
    (HNOTIN:n1 ∉ η),
  n1 ∉ (η.add_bv n2 z)
:= begin
  intros,
  rw env.not_in_split at *,
  cases HNOTIN,
  unfold freevar.env.add_bv,
  split,
  { simp, assumption },
  { simp, rw if_neg; assumption }
end

lemma env.not_in_add_b: ∀ (η:freevar.env) n1 n2 z
    (HNEQ:n1 ≠ n2)
    (HNOTIN:n1 ∉ η),
  n1 ∉ (η.add_b n2 z)
:= begin
  intros,
  rw env.not_in_split at *,
  cases HNOTIN,
  unfold freevar.env.add_b,
  split,
  { simp, rw if_neg; assumption },
  { simp, assumption }
end

lemma env.not_in_empty: ∀ n, n ∉ freevar.env.empty
:= begin
  intros, rw env.not_in_split,
  split; refl
end

-- replace_sb, repalce_sbv

lemma env.not_in_replace_sb: ∀ (η:freevar.env) n
    (HNOTIN:n ∉ η),
  η⟦sbool.var n⟧ = sbool.var n
:= begin
  intros,
  rw env.not_in_split at *,
  cases HNOTIN,
  unfold freevar.env.replace_sb,
  generalize H:η.b n = g,
  cases g,
  { refl },
  { rw HNOTIN_left at H, cases H }
end

lemma env.not_in_replace_sbv: ∀ (η:freevar.env) n sz
    (HNOTIN:n ∉ η),
  η⟦sbitvec.var sz n⟧ = sbitvec.var sz n
:= begin
  intros,
  rw env.not_in_split at *,
  cases HNOTIN,
  unfold freevar.env.replace_sbv,
  generalize H:η.bv n = g,
  cases g,
  { refl },
  { rw HNOTIN_right at H, cases H }
end

lemma env.in_replace_sbv: ∀ (η:freevar.env) n sz
    (HIN:∃ z, η.bv n = some z),
  ∃ z, η⟦sbitvec.var sz n⟧ = sbitvec.const sz z
:= begin
  intros,
  cases HIN with z HIN,
  unfold freevar.env.replace_sbv,
  rw HIN,
  unfold freevar.env.replace_sbv._match_1,
  cases z; unfold sbitvec.of_int,
  apply exists.intro, refl,
  apply exists.intro, refl
end

lemma env.sbv_var_or_const: ∀ (η:freevar.env) sz n,
  η⟦sbitvec.var sz n⟧ = sbitvec.var sz n ∨
  ∃ z, η⟦sbitvec.var sz n⟧ = sbitvec.const sz z
:= begin
  intros,
  unfold freevar.env.replace_sbv,
  generalize H: (η.bv n) = b,
  cases b,
  {
    unfold freevar.env.replace_sbv._match_1,
    left, refl
  },
  {
    unfold freevar.env.replace_sbv._match_1,
    right, cases b; unfold sbitvec.of_int,
    apply exists.intro, refl,
    apply exists.intro, refl
  }
end

lemma env.sb_var_or_const: ∀ (η:freevar.env) n,
  η⟦sbool.var n⟧ = sbool.var n ∨
  η⟦sbool.var n⟧ = sbool.tt ∨
  η⟦sbool.var n⟧ = sbool.ff
:= begin
  intros,
  unfold freevar.env.replace_sb,
  generalize H: (η.b n) = b,
  cases b,
  {
    unfold freevar.env.replace_sb._match_1,
    left, refl
  },
  {
    unfold freevar.env.replace_sb._match_1,
    right, cases b, right, refl, left, refl
  }
end

lemma env.not_in_add_bv_replace: ∀ (η:freevar.env) n n2 sz z
    (HNEQ:n ≠ n2),
  (η.add_bv n2 z)⟦sbitvec.var sz n⟧ = η⟦sbitvec.var sz n⟧
:= begin
  intros,
  unfold freevar.env.replace_sbv,
  unfold freevar.env.add_bv,
  simp,
  rw if_neg, assumption
end

lemma env.not_in_add_b_replace: ∀ (η:freevar.env) n n2 z
    (HNEQ:n ≠ n2),
  (η.add_b n2 z)⟦sbool.var n⟧ = η⟦sbool.var n⟧
:= begin
  intros,
  unfold freevar.env.replace_sb,
  unfold freevar.env.add_b,
  simp,
  rw if_neg, assumption
end

lemma env.add_b_replace_match: ∀ (η:freevar.env) n b,
  (freevar.env.add_b η n b)⟦sbool.var n⟧ = sbool.of_bool b
:= begin
  intros,
  unfold freevar.env.replace_sb,
  unfold freevar.env.add_b,
  simp, unfold freevar.env.replace_sb._match_1
end

lemma env.add_bv_replace_match: ∀ (η:freevar.env) n z sz,
  (freevar.env.add_bv η n z)⟦sbitvec.var sz n⟧ = sbitvec.of_int sz z
:= begin
  intros,
  unfold freevar.env.replace_sbv,
  unfold freevar.env.add_bv,
  simp, unfold freevar.env.replace_sbv._match_1
end

lemma env.add_bv_replace_sb: ∀ (η:freevar.env) n n' z,
  (freevar.env.add_bv η n z)⟦sbool.var n'⟧ = η⟦sbool.var n'⟧
:= begin
  intros,
  unfold freevar.env.replace_sb,
  unfold freevar.env.add_bv
end

lemma env.add_b_replace_sbv: ∀ (η:freevar.env) n n' b sz,
  (freevar.env.add_b η n b)⟦sbitvec.var sz n'⟧ = η⟦sbitvec.var sz n'⟧
:= begin
  intros,
  unfold freevar.env.replace_sbv,
  unfold freevar.env.add_b
end

lemma env.replace_sb_cases: ∀ s (η:freevar.env), 
  η⟦sbool.var s⟧ = sbool.var s ∨ η⟦sbool.var s⟧ = sbool.tt ∨ η⟦sbool.var s⟧ = sbool.ff
:= begin
  intros,
  unfold freevar.env.replace_sb,
  generalize Hb: η.b s = b',
  rw Hb at *, cases b'; unfold freevar.env.replace_sb._match_1,
  { left, refl },
  {
    right,
    cases b'; unfold sbool.of_bool; simp
  }
end

lemma env.replace_sbv_cases: ∀ sz s (η:freevar.env),
  η⟦sbitvec.var sz s⟧ = sbitvec.var sz s
    ∨ ∃ n, η⟦sbitvec.var sz s⟧ = sbitvec.const sz n
:= begin
  intros,
  unfold freevar.env.replace_sbv,
  generalize Hb: η.bv s = b',
  rw Hb at *, cases b'; unfold freevar.env.replace_sbv._match_1,
  { left, refl },
  {
    right,
    cases b'; unfold sbitvec.of_int,
    apply exists.intro, refl, apply exists.intro, refl
  }
end


lemma env.not_in_add_b_bv_bv_comm: ∀ (η:freevar.env) z,
  (∀ (v:sbool) n, n ∉ η → (η.add_bv n z)⟦v⟧ =
      (freevar.env.empty.add_bv n z)⟦η⟦v⟧⟧) ∧
  (∀ {sz} (v:sbitvec sz) n, n ∉ η → 
        (η.add_bv n z)⟦v⟧ = (freevar.env.empty.add_bv n z)⟦η⟦v⟧⟧)
:= begin
  intros,
  split,
  apply sbool.induction
      (λ v, ∀ n, n ∉ η → (η.add_bv n z)⟦v⟧ = (freevar.env.empty.add_bv n z)⟦η⟦v⟧⟧)
      (λ {sz} (v:sbitvec sz), ∀ n, n ∉ η → 
            (η.add_bv n z)⟦v⟧ = (freevar.env.empty.add_bv n z)⟦η⟦v⟧⟧),
  any_goals {
    apply sbitvec.induction
      (λ v, ∀ n, n ∉ η → (η.add_bv n z)⟦v⟧ = (freevar.env.empty.add_bv n z)⟦η⟦v⟧⟧)
      (λ {sz} (v:sbitvec sz), ∀ n, n ∉ η → 
            (η.add_bv n z)⟦v⟧ = (freevar.env.empty.add_bv n z)⟦η⟦v⟧⟧),
  },
  any_goals { intros, refl },
  any_goals {
    intros,
    unfold freevar.env.add_bv,
    unfold freevar.env.replace_sb,
    simp,
    unfold freevar.env.empty,
    generalize HG: η.b s = b',
    cases b',
    {
      unfold freevar.env.replace_sb._match_1,
      unfold freevar.env.replace_sb,
    },
    {
      unfold freevar.env.replace_sb._match_1,
      rw env.replace_sb_of_bool, done
    }
  },
  any_goals {
    intros b1 b2 H1 H2 n' HNOTIN',
    unfold freevar.env.replace_sb at *,
    rw [H1, H2]; assumption
  },
  any_goals {
    intros b1 b2 b3 H1 H2 H3 n' HNOTIN',
    unfold freevar.env.replace_sb at *,
    rw [H1, H2, H3]; assumption
  },
  any_goals {
    intros b H n' HNOTIN',
    unfold freevar.env.replace_sb at *,
    rw [H], assumption
  },
  any_goals {
    intros sz b1 b2 H1 H2 n' HNOTIN',
    unfold freevar.env.replace_sb at *,
    rw [H1, H2]; assumption
  },
  any_goals {
    intros,
    unfold freevar.env.replace_sbv at *, done
  },
  any_goals {
    intros sz n',
    intros n'' HNOTIN',
    have HEQ:decidable (n' = n''), apply_instance,
    cases HEQ,
    {
      have H:= env.sbv_var_or_const η sz n',
      cases H,
      {
        rw env.not_in_add_bv_replace,
        rw H,
        rw env.not_in_add_bv_replace,
        rw env.empty_replace_sbv,
        assumption, assumption
      },
      {
        cases H with z' H,
        rw env.not_in_add_bv_replace,
        rw H,
        unfold freevar.env.replace_sbv,
        assumption
      }
    },
    {
      rw HEQ,
      rw env.add_bv_replace_match,
      rw env.not_in_replace_sbv,
      rw env.add_bv_replace_match,
      assumption
    }
  },
  any_goals {
    intros sz v1 v2 H1 H2 n' HNOTIN',
    unfold freevar.env.replace_sbv at *,
    rw [H1, H2]; assumption
  },
  any_goals {
    intros sz v sz' H n' HNOTIN',
    unfold freevar.env.replace_sbv at *,
    rw H, assumption
  },
  any_goals {
    intros sz sz' v highbit lowbit HH H n' HNOTIN',
    unfold freevar.env.replace_sbv at *,
    rw H, assumption
  },
  any_goals {
    intros sz v1 v2 v3 H1 H2 H3 n' HNOTIN',
    unfold freevar.env.replace_sbv at *,
    rw [H1, H2, H3]; assumption
  }
end

lemma env.not_in_add_bv_b_comm: ∀ (η:freevar.env) z (v:sbool) n,
  n ∉ η → (η.add_bv n z)⟦v⟧ = (freevar.env.empty.add_bv n z)⟦η⟦v⟧⟧
:= begin
  intros, apply (and.elim_left (env.not_in_add_b_bv_bv_comm η z)),
  assumption
end

lemma env.not_in_add_bv_bv_comm: ∀ (η:freevar.env) z {sz} (v:sbitvec sz) n,
  n ∉ η → (η.add_bv n z)⟦v⟧ = (freevar.env.empty.add_bv n z)⟦η⟦v⟧⟧
:= begin
  intros, apply (and.elim_right (env.not_in_add_b_bv_bv_comm η z)),
  assumption
end




lemma env.not_in_add_b_bv_b_comm: ∀ (η:freevar.env) z,
  (∀ (v:sbool) n, n ∉ η → (η.add_b n z)⟦v⟧ =
      (freevar.env.empty.add_b n z)⟦η⟦v⟧⟧) ∧
  (∀ {sz} (v:sbitvec sz) n, n ∉ η → 
        (η.add_b n z)⟦v⟧ = (freevar.env.empty.add_b n z)⟦η⟦v⟧⟧)
:= begin
  intros,
  split,
  apply sbool.induction
      (λ v, ∀ n, n ∉ η → (η.add_b n z)⟦v⟧ = (freevar.env.empty.add_b n z)⟦η⟦v⟧⟧)
      (λ {sz} (v:sbitvec sz), ∀ n, n ∉ η → 
            (η.add_b n z)⟦v⟧ = (freevar.env.empty.add_b n z)⟦η⟦v⟧⟧),
  any_goals {
    apply sbitvec.induction
      (λ v, ∀ n, n ∉ η → (η.add_b n z)⟦v⟧ = (freevar.env.empty.add_b n z)⟦η⟦v⟧⟧)
      (λ {sz} (v:sbitvec sz), ∀ n, n ∉ η → 
            (η.add_b n z)⟦v⟧ = (freevar.env.empty.add_b n z)⟦η⟦v⟧⟧),
  },
  any_goals { intros, refl },
  any_goals {
    intros n',
    intros n'' HNOTIN',
    have HEQ:decidable (n' = n''), apply_instance,
    cases HEQ,
    {
      have H:= env.sb_var_or_const η n',
      cases H,
      {
        rw env.not_in_add_b_replace,
        rw H,
        rw env.not_in_add_b_replace,
        rw env.empty_replace_sb,
        assumption, assumption
      },
      {
        cases H,
        any_goals {rw env.not_in_add_b_replace,
          rw H,
          unfold freevar.env.replace_sb,
          assumption }
      }
    },
    {
      rw HEQ,
      rw env.add_b_replace_match,
      rw env.not_in_replace_sb,
      rw env.add_b_replace_match,
      assumption
    }
  },
  any_goals {
    intros b1 b2 H1 H2 n' HNOTIN',
    unfold freevar.env.replace_sb at *,
    rw [H1, H2]; assumption
  },
  any_goals {
    intros b1 b2 b3 H1 H2 H3 n' HNOTIN',
    unfold freevar.env.replace_sb at *,
    rw [H1, H2, H3]; assumption
  },
  any_goals {
    intros b H n' HNOTIN',
    unfold freevar.env.replace_sb at *,
    rw [H], assumption
  },
  any_goals {
    intros sz b1 b2 H1 H2 n' HNOTIN',
    unfold freevar.env.replace_sb at *,
    rw [H1, H2]; assumption
  },
  any_goals {
    intros,
    unfold freevar.env.replace_sbv at *, done
  },
  any_goals {
    intros,
    unfold freevar.env.add_b,
    unfold freevar.env.replace_sbv,
    simp,
    unfold freevar.env.empty,
    generalize HG: η.bv n = b',
    cases b',
    {
      unfold freevar.env.replace_sbv._match_1,
      unfold freevar.env.replace_sbv,
    },
    {
      unfold freevar.env.replace_sbv._match_1,
      simp,
      rw env.replace_sbv_of_int, done
    }
  },
  any_goals {
    intros sz v1 v2 H1 H2 n' HNOTIN',
    unfold freevar.env.replace_sbv at *,
    rw [H1, H2]; assumption
  },
  any_goals {
    intros sz v sz' H n' HNOTIN',
    unfold freevar.env.replace_sbv at *,
    rw H, assumption
  },
  any_goals {
    intros sz sz' v highbit lowbit HH H n' HNOTIN',
    unfold freevar.env.replace_sbv at *,
    rw H, assumption
  },
  any_goals {
    intros sz v1 v2 v3 H1 H2 H3 n' HNOTIN',
    unfold freevar.env.replace_sbv at *,
    rw [H1, H2, H3]; assumption
  }
end

lemma env.not_in_add_b_b_comm: ∀ (η:freevar.env) z (v:sbool) n,
  n ∉ η → (η.add_b n z)⟦v⟧ = (freevar.env.empty.add_b n z)⟦η⟦v⟧⟧
:= begin
  intros, apply (and.elim_left (env.not_in_add_b_bv_b_comm η z)),
  assumption
end

lemma env.not_in_add_b_bv_comm: ∀ (η:freevar.env) z {sz} (v:sbitvec sz) n,
  n ∉ η → (η.add_b n z)⟦v⟧ = (freevar.env.empty.add_b n z)⟦η⟦v⟧⟧
:= begin
  intros, apply (and.elim_right (env.not_in_add_b_bv_b_comm η z)),
  assumption
end

lemma env.not_in_add_bv_valty_comm: ∀ (η:freevar.env) (vv:valty_smt) n z,
  n ∉ η → (η.add_bv n z)⟦vv⟧ = (freevar.env.empty.add_bv n z)⟦η⟦vv⟧⟧
:= begin
  intros,
  cases vv with sz iv pv,
  unfold freevar.env.replace_valty,
  simp,
  rw env.not_in_add_bv_bv_comm,
  rw env.not_in_add_bv_b_comm,
  split, refl, refl,
  assumption, assumption
end

lemma env.not_in_add_b_valty_comm: ∀ (η:freevar.env) (vv:valty_smt) n z,
  n ∉ η → (η.add_b n z)⟦vv⟧ = (freevar.env.empty.add_b n z)⟦η⟦vv⟧⟧
:= begin
  intros,
  cases vv with sz iv pv,
  unfold freevar.env.replace_valty,
  simp,
  rw env.not_in_add_b_bv_comm,
  rw env.not_in_add_b_b_comm,
  split, refl, refl,
  assumption, assumption
end

lemma env.not_in_add_bv_irstate_comm: ∀ (η:freevar.env) (ss:irstate irsem_smt) n z,
  n ∉ η → (η.add_bv n z)⟦ss⟧ = (freevar.env.empty.add_bv n z)⟦η⟦ss⟧⟧
:= begin
  intros,
  cases ss,
  unfold freevar.env.replace,
  rw ← irstate.setub_apply_to_values,
  rw ← irstate.setub_apply_to_values,
  rw ← irstate.setub_apply_to_values,
  rw ← irstate.setub_apply_to_values,
  unfold irstate.getub,
  unfold irstate.setub,
  unfold irstate.apply_to_values,
  unfold regfile.apply_to_values,
  simp,
  rw prod_inj,
  simp,
  split,
  {
    rw env.not_in_add_bv_b_comm, assumption
  },
  {
    induction ss_snd,
    { refl },
    {
      simp,
      rw ss_snd_ih,
      cases ss_snd_hd with rn v,
      cases v with sz iv pv,
      rw env.not_in_add_bv_valty_comm,
      assumption
    }
  }
end

lemma env.not_in_add_b_irstate_comm: ∀ (η:freevar.env) (ss:irstate irsem_smt) n z,
  n ∉ η → (η.add_b n z)⟦ss⟧ = (freevar.env.empty.add_b n z)⟦η⟦ss⟧⟧
:= begin
  intros,
  cases ss,
  unfold freevar.env.replace,
  rw ← irstate.setub_apply_to_values,
  rw ← irstate.setub_apply_to_values,
  rw ← irstate.setub_apply_to_values,
  rw ← irstate.setub_apply_to_values,
  unfold irstate.getub,
  unfold irstate.setub,
  unfold irstate.apply_to_values,
  unfold regfile.apply_to_values,
  simp,
  rw prod_inj,
  simp,
  split,
  {
    rw env.not_in_add_b_b_comm, assumption
  },
  {
    induction ss_snd,
    { refl },
    {
      simp,
      rw ss_snd_ih,
      cases ss_snd_hd with rn v,
      cases v with sz iv pv,
      rw env.not_in_add_b_valty_comm,
      assumption
    }
  }
end

lemma env.has_only_shuffle: ∀ {η:freevar.env} (s:string) (l1 l2:list string),
  env.has_only η (s::(l1 ++ l2)) ↔ env.has_only η (l1 ++ s::l2)
:= begin
  intros, rw ← list.cons_append,
  unfold env.has_only,
  split,
  {
    intros, simp, simp at a,
    rw or.comm, rw or.assoc,
    rw @or.comm (name ∈ l2) (name ∈ l1), apply a
  },
  {
    intros, simp, simp at a,
    rw or.comm, rw or.assoc,
    rw @or.comm (name ∈ l2) (name = s), apply a
  }
end

lemma env.has_only_shuffle2: ∀ {η:freevar.env} (s1 s2:string) (l:list string),
  env.has_only η (s1::s2::l) ↔ env.has_only η (s2::s1::l)
:= begin
  intros,
  unfold env.has_only,
  split,
  {
    intros, simp, simp at a,
    rw or.comm, rw or.assoc,
    rw @or.comm (name ∈ l) (name = s2), apply a
  },
  {
    intros, simp, simp at a,
    rw or.comm, rw or.assoc,
    rw @or.comm (name ∈ l) (name = s1), apply a
  }
end

lemma env.has_only_added2: ∀ {η η':freevar.env} {n1 n2:string}
    {l:list string}
    (H1: env.has_only η l)
    (H2: env.added2 η n1 n2 η'),
  env.has_only η' (n1::n2::l)
:= begin
  intros,
  unfold env.added2 at H2,
  cases H2,
  unfold env.has_only at *,
  intros,
  simp,
  rw H1,
  split,
  { intros, apply H2_right, rw or.comm, rw or.assoc, assumption },
  {
    intros,
    rw ← decidable.not_not_iff (name ∈ η') at a,
    rw ← decidable.not_not_iff (name = n1 ∨ name = n2 ∨ name ∈ η),
    intros H0,
    rw decidable.not_or_iff_and_not at H0,
    rw decidable.not_or_iff_and_not at H0,
    cases H0, cases H0_right,
    apply a,
    apply H2_left, assumption, split; assumption
  }
end

lemma env.has_only_not_in: ∀ {η:freevar.env} {l n}
  (H:env.has_only η l) (HNOTIN:n ∉ l), n ∉ η
:= begin
  intros,
  unfold env.has_only at H,
  intros H0,
  apply HNOTIN, rw H, assumption
end

-- get_value

lemma get_value_replace: ∀ (ss:irstate_smt) (op:operand)
    (η:freevar.env) (t:ty),
  get_value irsem_smt (η⟦ss⟧) op t = η⟦get_value irsem_smt ss op t⟧'
:= begin
  intros,
  cases op,
  { -- operand.reg
    cases op,
    unfold get_value,
    apply getreg_replace, refl
  },
  {
    cases op,
    cases t,
    {
      unfold get_value,
      have H0: decidable (0 < t), apply_instance,
      cases H0,
      { rw dif_neg, assumption },
      {
        rw dif_pos,
        simp,
        have H1: decidable (within_signed_range ⟨t, H0⟩ op), apply_instance,
        cases H1,
        {
          rw if_neg,
          {
            have H2: decidable (↑(int_min_nat ⟨t, H0⟩) ≤ op ∧ op ≤ ↑(all_one_nat ⟨t, H0⟩)),
              apply_instance,
            cases H2,
            { rw if_neg, apply H2 },
            { rw if_pos,
              unfold uint_like.from_z,
              unfold apply,
              unfold freevar.env.replace_valty,
              generalize HCONST: op + -↑(2^t) = c,
              cases c,
              { unfold sbitvec.of_int, unfold freevar.env.replace_sbv, refl },
              { unfold sbitvec.of_int, unfold freevar.env.replace_sbv, refl },
              assumption
            }
          },
          { assumption }
        },
        { rw if_pos,
          unfold uint_like.from_z,
          unfold apply,
          unfold freevar.env.replace_valty,
          cases op,
          { unfold sbitvec.of_int, unfold freevar.env.replace_sbv, refl },
          { unfold sbitvec.of_int, unfold freevar.env.replace_sbv, refl },
          assumption
        }
      }
    },
    { unfold get_value }
  }
end

end spec
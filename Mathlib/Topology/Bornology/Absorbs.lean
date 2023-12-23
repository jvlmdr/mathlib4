/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Topology.Bornology.Constructions

#align_import analysis.locally_convex.basic from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Definitions of `Absorbs` and `Absorbent`

Let `M` act on `α`, let `A` and `B` be sets in `α`.
We say that `A` *absorbs* `B` if for sufficiently large `a : M`, we have `B ⊆ a • A`.
Formally, "for sufficiently large `a : M`" means "for all but a bounded set of `a`".

Traditionally, this definition is formulated
for the action of a (semi)normed ring on a module over that ring.

We formulate it in a more general settings for two reasons:

- this way we don't have to depend on metric spaces, normed rings etc;
- some proofs look nicer with this definition than with something like
  `∃ r : ℝ, ∀ a : R, r ≤ ‖a‖ → B ⊆ a • A`.

-/

open Set Bornology Filter
open scoped Pointwise

assert_not_exists Real

section Defs

variable (M : Type*) {α : Type*} [Bornology M] [SMul M α]

/-- A set `s` absorbs another set `t` if `t` is contained in all scalings of `s`
by all but a bounded set of elements. -/
def Absorbs (s t : Set α) : Prop :=
  ∀ᶠ a in cobounded M, t ⊆ a • s
#align absorbs Absorbs

/-- A set is *absorbent* if it absorbs every singleton. -/
def Absorbent (s : Set α) : Prop :=
  ∀ x : α, Absorbs M s {x}
#align absorbent Absorbent

end Defs

namespace Absorbs

section SMul

variable {M α : Type*} [Bornology M] [SMul M α] {s t : Set α}

protected lemma empty : Absorbs M s ∅ := by simp [Absorbs]
#align absorbs_empty Absorbs.empty

protected lemma eventually (h : Absorbs M s t) : ∀ᶠ a in cobounded M, t ⊆ a • s := h

@[simp] lemma of_boundedSpace [BoundedSpace M] : Absorbs M s t := by simp [Absorbs]

lemma mono_left {s'} (h : Absorbs M s t) (hs : s ⊆ s') : Absorbs M s' t :=
  h.mono fun _a ha ↦ ha.trans <| smul_set_mono hs
#align absorbs.mono_left Absorbs.mono_left

lemma mono_right {t'} (h : Absorbs M s t) (ht : t' ⊆ t) : Absorbs M s t' :=
  h.mono fun _ ↦ ht.trans
#align absorbs.mono_right Absorbs.mono_right

lemma mono {s' t'} (h : Absorbs M s t) (hs : s ⊆ s') (ht : t' ⊆ t) : Absorbs M s' t' :=
  (h.mono_left hs).mono_right ht
#align absorbs.mono Absorbs.mono

@[simp]
lemma _root_.absorbs_union {t₁ t₂} : Absorbs M s (t₁ ∪ t₂) ↔ Absorbs M s t₁ ∧ Absorbs M s t₂ := by
  simp [Absorbs]
#align absorbs_union absorbs_union

protected lemma union {t₁ t₂} (h₁ : Absorbs M s t₁) (h₂ : Absorbs M s t₂) : Absorbs M s (t₁ ∪ t₂) :=
  absorbs_union.2 ⟨h₁, h₂⟩
#align absorbs.union Absorbs.union

lemma _root_.Set.Finite.absorbs_sUnion {T : Set (Set α)} (hT : T.Finite) :
    Absorbs M s (⋃₀ T) ↔ ∀ t ∈ T, Absorbs M s t := by
  simp [Absorbs, hT]

protected lemma sUnion {T : Set (Set α)} (hT : T.Finite) (hs : ∀ t ∈ T, Absorbs M s t) :
    Absorbs M s (⋃₀ T) :=
  hT.absorbs_sUnion.2 hs

@[simp]
lemma _root_.absorbs_iUnion {ι : Sort*} [Finite ι] {t : ι → Set α} :
    Absorbs M s (⋃ i, t i) ↔ ∀ i, Absorbs M s (t i) :=
  (finite_range t).absorbs_sUnion.trans forall_range_iff

protected lemma iUnion {ι : Sort*} [Finite ι] {t : ι → Set α} (h : ∀ i, Absorbs M s (t i)) :
    Absorbs M s (⋃ i, t i) :=
  absorbs_iUnion.2 h

lemma _root_.Set.Finite.absorbs_biUnion {ι : Type*} {t : ι → Set α} {I : Set ι} (hI : I.Finite) :
    Absorbs M s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, Absorbs M s (t i) := by
  simp [Absorbs, hI]
#align set.finite.absorbs_Union Set.Finite.absorbs_biUnion

protected lemma biUnion {ι : Type*} {t : ι → Set α} {I : Set ι} (hI : I.Finite)
    (h : ∀ i ∈ I, Absorbs M s (t i)) : Absorbs M s (⋃ i ∈ I, t i) :=
  hI.absorbs_biUnion.2 h

@[simp]
lemma _root_.absorbs_biUnion_finset {ι : Type*} {t : ι → Set α} {I : Finset ι} :
    Absorbs M s (⋃ i ∈ I, t i) ↔ ∀ i ∈ I, Absorbs M s (t i) :=
  I.finite_toSet.absorbs_biUnion
#align absorbs_Union_finset absorbs_biUnion_finset

protected lemma biUnion_finset {ι : Type*} {t : ι → Set α} {I : Finset ι}
    (h : ∀ i ∈ I, Absorbs M s (t i)) : Absorbs M s (⋃ i ∈ I, t i) :=
  absorbs_biUnion_finset.2 h

end SMul

protected lemma add {M E : Type*} [Bornology M] [AddZeroClass E] [DistribSMul M E]
    {s₁ s₂ t₁ t₂ : Set E} (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) :
    Absorbs M (s₁ + s₂) (t₁ + t₂) :=
  h₂.mp <| h₁.eventually.mono fun x hx₁ hx₂ ↦ by rw [smul_add]; exact add_subset_add hx₁ hx₂
#align absorbs.add Absorbs.add

protected lemma zero {M₀ E : Type*} [Bornology M₀] [Zero M₀] [Zero E] [SMulZeroClass M₀ E]
    {s : Set E} (hs : 0 ∈ s) : Absorbs M₀ s 0 :=
  eventually_of_forall fun _ ↦ zero_subset.2 <| zero_mem_smul_set hs

section GroupWithZero

variable {G₀ α : Type*} [GroupWithZero G₀] [Bornology G₀] [MulAction G₀ α] {s t u : Set α}

@[simp]
protected lemma univ : Absorbs G₀ univ s :=
  (eventually_ne_cobounded 0).mono fun a ha ↦ by rw [smul_set_univ₀ ha]; apply subset_univ

lemma _root_.Set.Finite.absorbs_sInter {S : Set (Set α)} (hS : S.Finite) :
    Absorbs G₀ (⋂₀ S) t ↔ ∀ s ∈ S, Absorbs G₀ s t := by
  simp only [Absorbs, ← hS.eventually_all]
  refine eventually_congr <| (eventually_ne_cobounded 0).mono fun a ha ↦ ?_
  simp only [← preimage_smul_inv₀ ha, preimage_sInter, subset_iInter_iff]

protected lemma sInter {S : Set (Set α)} (hs : S.Finite) (ht : ∀ s ∈ S, Absorbs G₀ s t) :
    Absorbs G₀ (⋂₀ S) t :=
  hs.absorbs_sInter.2 ht

@[simp]
lemma _root_.absorbs_inter : Absorbs G₀ (s ∩ t) u ↔ Absorbs G₀ s u ∧ Absorbs G₀ t u := by
  simpa using ((finite_singleton t).insert s).absorbs_sInter
#align absorbs_inter absorbs_inter

protected lemma inter (hs : Absorbs G₀ s u) (ht : Absorbs G₀ t u) : Absorbs G₀ (s ∩ t) u :=
  absorbs_inter.2 ⟨hs, ht⟩
#align absorbs.inter Absorbs.inter

@[simp]
lemma _root_.absorbs_iInter {ι : Sort*} [Finite ι] {s : ι → Set α} :
    Absorbs G₀ (⋂ i, s i) t ↔ ∀ i, Absorbs G₀ (s i) t :=
  (finite_range s).absorbs_sInter.trans forall_range_iff

protected lemma iInter {ι : Sort*} [Finite ι] {s : ι → Set α} (h : ∀ i, Absorbs G₀ (s i) t) :
    Absorbs G₀ (⋂ i, s i) t :=
  absorbs_iInter.2 h

lemma _root_.Set.Finite.absorbs_biInter {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set α} :
    Absorbs G₀ (⋂ i ∈ I, s i) t ↔ ∀ i ∈ I, Absorbs G₀ (s i) t := by
  simpa only [sInter_image, ball_image_iff] using (hI.image s).absorbs_sInter

protected lemma biInter {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set α}
    (h : ∀ i ∈ I, Absorbs G₀ (s i) t) : Absorbs G₀ (⋂ i ∈ I, s i) t :=
  hI.absorbs_biInter.2 h

@[simp]
lemma _root_.absorbs_zero_iff [NeBot (cobounded G₀)] {E : Type*} [AddMonoid E]
    [DistribMulAction G₀ E] {s : Set E} : Absorbs G₀ s 0 ↔ 0 ∈ s := by
  refine ⟨fun h ↦ ?_, .zero⟩
  rcases (h.and (eventually_ne_cobounded 0)).exists with ⟨c, hc, hc₀⟩
  rcases hc rfl with ⟨x, hx, hx₀⟩
  rwa [← smul_zero c⁻¹, ← hx₀, inv_smul_smul₀ hc₀]
#align absorbs_zero_iff absorbs_zero_iff

end GroupWithZero

end Absorbs

section AddGroup

variable {M E : Type*} [Monoid M] [AddGroup E] [DistribMulAction M E] [Bornology M]

@[simp]
lemma absorbs_neg_neg {s t : Set E} : Absorbs M (-s) (-t) ↔ Absorbs M s t := by simp [Absorbs]

alias ⟨Absorbs.of_neg_neg, Absorbs.neg_neg⟩ := absorbs_neg_neg
#align absorbs.neg Absorbs.neg_neg

lemma Absorbs.sub {s₁ s₂ t₁ t₂ : Set E} (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) :
    Absorbs M (s₁ - s₂) (t₁ - t₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_neg
#align absorbs.sub Absorbs.sub

end AddGroup

namespace Absorbent

variable {M α : Type*} [Bornology M] [SMul M α] {s t : Set α}

protected theorem subset (ht : Absorbent M s) (hsub : s ⊆ t) : Absorbent M t := fun x ↦
  (ht x).mono_left hsub
#align absorbent.subset Absorbent.subset

theorem _root_.absorbent_iff_forall_absorbs_singleton : Absorbent M s ↔ ∀ x, Absorbs M s {x} := .rfl
#align absorbent_iff_forall_absorbs_singleton absorbent_iff_forall_absorbs_singleton

protected theorem absorbs (hs : Absorbent M s) {x : α} : Absorbs M s {x} := hs x
#align absorbent.absorbs Absorbent.absorbs

#noalign absorbent_iff_nonneg_lt

theorem absorbs_finite (hs : Absorbent M s) (ht : t.Finite) : Absorbs M s t := by
  rw [← Set.biUnion_of_singleton t]
  exact ht.absorbs_biUnion.mpr fun _ _ => hs.absorbs
#align absorbent.absorbs_finite Absorbent.absorbs_finite

end Absorbent

section GroupWithZero

variable {G₀ α E : Type*} [GroupWithZero G₀] [Bornology G₀] [MulAction G₀ α]

lemma absorbent_univ : Absorbent G₀ (univ : Set α) := fun _ ↦ .univ
#align absorbent_univ absorbent_univ

lemma absorbent_iff_inv_smul {s : Set α} :
    Absorbent G₀ s ↔ ∀ x, ∀ᶠ c in cobounded G₀, c⁻¹ • x ∈ s :=
  forall_congr' fun x ↦ eventually_congr <| (eventually_ne_cobounded 0).mono fun c hc ↦ by
    rw [singleton_subset_iff, ← preimage_smul_inv₀ hc, mem_preimage]

lemma Absorbent.zero_mem [NeBot (cobounded G₀)] [AddMonoid E] [DistribMulAction G₀ E]
    {s : Set E} (hs : Absorbent G₀ s) : (0 : E) ∈ s :=
  absorbs_zero_iff.1 (hs 0)
#align absorbent.zero_mem Absorbent.zero_mem

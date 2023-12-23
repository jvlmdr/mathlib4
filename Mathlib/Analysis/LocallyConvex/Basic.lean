/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Bhavik Mehta, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Bornology.Absorbs

#align_import analysis.locally_convex.basic from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Local convexity

This file defines absorbent and balanced sets.

An absorbent set is one that "surrounds" the origin. The idea is made precise by requiring that any
point belongs to all large enough scalings of the set. This is the vector world analog of a
topological neighborhood of the origin.

A balanced set is one that is everywhere around the origin. This means that `a • s ⊆ s` for all `a`
of norm less than `1`.

## Main declarations

For a module over a normed ring:
* `Absorbs`: A set `s` absorbs a set `t` if all large scalings of `s` contain `t`.
* `Absorbent`: A set `s` is absorbent if every point eventually belongs to all large scalings of
  `s`.
* `Balanced`: A set `s` is balanced if `a • s ⊆ s` for all `a` of norm less than `1`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

absorbent, balanced, locally convex, LCTVS
-/


open Set

open Pointwise Topology

variable {𝕜 𝕝 E : Type*} {ι : Sort*} {κ : ι → Sort*}

section SeminormedRing

variable [SeminormedRing 𝕜]

section SMul

variable [SMul 𝕜 E] {s t u v A B : Set E}
variable (𝕜)

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a` has norm at most `1`. -/
def Balanced (A : Set E) :=
  ∀ a : 𝕜, ‖a‖ ≤ 1 → a • A ⊆ A
#align balanced Balanced

variable {𝕜}

lemma absorbs_iff_norm : Absorbs 𝕜 A B ↔ ∃ r, ∀ c : 𝕜, r ≤ ‖c‖ → B ⊆ c • A :=
  Filter.atTop_basis.cobounded_of_norm.eventually_iff.trans <| by simp only [true_and]; rfl

alias ⟨_, Absorbs.of_norm⟩ := absorbs_iff_norm

lemma Absorbs.exists_pos (h : Absorbs 𝕜 A B) : ∃ r > 0, ∀ c : 𝕜, r ≤ ‖c‖ → B ⊆ c • A :=
  let ⟨r, hr₁, hr⟩ := (Filter.atTop_basis' 1).cobounded_of_norm.eventually_iff.1 h
  ⟨r, one_pos.trans_le hr₁, hr⟩

theorem balanced_iff_smul_mem : Balanced 𝕜 s ↔ ∀ ⦃a : 𝕜⦄, ‖a‖ ≤ 1 → ∀ ⦃x : E⦄, x ∈ s → a • x ∈ s :=
  forall₂_congr fun _a _ha => smul_set_subset_iff
#align balanced_iff_smul_mem balanced_iff_smul_mem

alias ⟨Balanced.smul_mem, _⟩ := balanced_iff_smul_mem
#align balanced.smul_mem Balanced.smul_mem

@[simp]
theorem balanced_empty : Balanced 𝕜 (∅ : Set E) := fun _ _ => by rw [smul_set_empty]
#align balanced_empty balanced_empty

@[simp]
theorem balanced_univ : Balanced 𝕜 (univ : Set E) := fun _a _ha => subset_univ _
#align balanced_univ balanced_univ

theorem Balanced.union (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∪ B) := fun _a ha =>
  smul_set_union.subset.trans <| union_subset_union (hA _ ha) <| hB _ ha
#align balanced.union Balanced.union

theorem Balanced.inter (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∩ B) := fun _a ha =>
  smul_set_inter_subset.trans <| inter_subset_inter (hA _ ha) <| hB _ ha
#align balanced.inter Balanced.inter

theorem balanced_iUnion {f : ι → Set E} (h : ∀ i, Balanced 𝕜 (f i)) : Balanced 𝕜 (⋃ i, f i) :=
  fun _a ha => (smul_set_iUnion _ _).subset.trans <| iUnion_mono fun _ => h _ _ ha
#align balanced_Union balanced_iUnion

theorem balanced_iUnion₂ {f : ∀ i, κ i → Set E} (h : ∀ i j, Balanced 𝕜 (f i j)) :
    Balanced 𝕜 (⋃ (i) (j), f i j) :=
  balanced_iUnion fun _ => balanced_iUnion <| h _
#align balanced_Union₂ balanced_iUnion₂

theorem balanced_iInter {f : ι → Set E} (h : ∀ i, Balanced 𝕜 (f i)) : Balanced 𝕜 (⋂ i, f i) :=
  fun _a ha => (smul_set_iInter_subset _ _).trans <| iInter_mono fun _ => h _ _ ha
#align balanced_Inter balanced_iInter

theorem balanced_iInter₂ {f : ∀ i, κ i → Set E} (h : ∀ i j, Balanced 𝕜 (f i j)) :
    Balanced 𝕜 (⋂ (i) (j), f i j) :=
  balanced_iInter fun _ => balanced_iInter <| h _
#align balanced_Inter₂ balanced_iInter₂

variable [SMul 𝕝 E] [SMulCommClass 𝕜 𝕝 E]

theorem Balanced.smul (a : 𝕝) (hs : Balanced 𝕜 s) : Balanced 𝕜 (a • s) := fun _b hb =>
  (smul_comm _ _ _).subset.trans <| smul_set_mono <| hs _ hb
#align balanced.smul Balanced.smul

end SMul

section Module

variable [AddCommGroup E] [Module 𝕜 E] {s s₁ s₂ t t₁ t₂ : Set E}

theorem Balanced.neg : Balanced 𝕜 s → Balanced 𝕜 (-s) :=
  forall₂_imp fun _ _ h => (smul_set_neg _ _).subset.trans <| neg_subset_neg.2 h
#align balanced.neg Balanced.neg

theorem Balanced.add (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s + t) := fun _a ha =>
  (smul_add _ _ _).subset.trans <| add_subset_add (hs _ ha) <| ht _ ha
#align balanced.add Balanced.add

theorem Balanced.sub (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s - t) := by
  simp_rw [sub_eq_add_neg]
  exact hs.add ht.neg
#align balanced.sub Balanced.sub

theorem balanced_zero : Balanced 𝕜 (0 : Set E) := fun _a _ha => (smul_zero _).subset
#align balanced_zero balanced_zero

end Module

end SeminormedRing

section NormedField

variable [NormedField 𝕜] [NormedRing 𝕝] [NormedSpace 𝕜 𝕝] [AddCommGroup E] [Module 𝕜 E]
  [SMulWithZero 𝕝 E] [IsScalarTower 𝕜 𝕝 E] {s t u v A B : Set E} {x : E} {a b : 𝕜}

/-- Scalar multiplication (by possibly different types) of a balanced set is monotone. -/
theorem Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} {b : 𝕜} (h : ‖a‖ ≤ ‖b‖) : a • s ⊆ b • s := by
  obtain rfl | hb := eq_or_ne b 0
  · rw [norm_zero] at h
    rw [norm_eq_zero.1 (h.antisymm <| norm_nonneg _)]
    obtain rfl | h := s.eq_empty_or_nonempty
    · simp_rw [smul_set_empty]; rfl
    · simp_rw [zero_smul_set h]; rfl
  rintro _ ⟨x, hx, rfl⟩
  refine' ⟨b⁻¹ • a • x, _, smul_inv_smul₀ hb _⟩
  rw [← smul_assoc]
  refine' hs _ _ (smul_mem_smul_set hx)
  rw [norm_smul, norm_inv, ← div_eq_inv_mul]
  exact div_le_one_of_le h (norm_nonneg _)
#align balanced.smul_mono Balanced.smul_mono

/-- A balanced set absorbs itself. -/
theorem Balanced.absorbs_self (hA : Balanced 𝕜 A) : Absorbs 𝕜 A A := by
  refine' ⟨1, zero_lt_one, fun a ha x hx => _⟩
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.1 <| zero_lt_one.trans_le ha)]
  refine' hA a⁻¹ _ (smul_mem_smul_set hx)
  rw [norm_inv]
  exact inv_le_one ha
#align balanced.absorbs_self Balanced.absorbs_self

theorem Balanced.subset_smul (hA : Balanced 𝕜 A) (ha : 1 ≤ ‖a‖) : A ⊆ a • A := by
  refine' (subset_set_smul_iff₀ _).2 (hA a⁻¹ _)
  · rintro rfl
    rw [norm_zero] at ha
    exact zero_lt_one.not_le ha
  · rw [norm_inv]
    exact inv_le_one ha
#align balanced.subset_smul Balanced.subset_smul

theorem Balanced.smul_eq (hA : Balanced 𝕜 A) (ha : ‖a‖ = 1) : a • A = A :=
  (hA _ ha.le).antisymm <| hA.subset_smul ha.ge
#align balanced.smul_eq Balanced.smul_eq

theorem Balanced.mem_smul_iff (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖) : a • x ∈ s ↔ b • x ∈ s := by
  obtain rfl | hb := eq_or_ne b 0
  · rw [norm_zero, norm_eq_zero] at h
    rw [h]
  have ha : a ≠ 0 := norm_ne_zero_iff.1 (ne_of_eq_of_ne h <| norm_ne_zero_iff.2 hb)
  constructor <;> intro h' <;> [rw [← inv_mul_cancel_right₀ ha b];
      rw [← inv_mul_cancel_right₀ hb a]] <;>
    · rw [← smul_eq_mul, smul_assoc]
      refine' hs.smul_mem _ h'
      simp [← h, ha]
#align balanced.mem_smul_iff Balanced.mem_smul_iff

theorem Balanced.neg_mem_iff (hs : Balanced 𝕜 s) : -x ∈ s ↔ x ∈ s := by
  convert hs.mem_smul_iff (x := x) (norm_neg 1) using 0;
  simp only [neg_smul, one_smul 𝕜 x]
#align balanced.neg_mem_iff Balanced.neg_mem_iff

variable [TopologicalSpace E] [ContinuousSMul 𝕜 E]

/-- Every neighbourhood of the origin is absorbent. -/
theorem absorbent_nhds_zero (hA : A ∈ 𝓝 (0 : E)) : Absorbent 𝕜 A :=
  absorbent_iff_inv_smul.2 fun x ↦ Filter.tendsto_inv₀_cobounded.smul tendsto_const_nhds <| by
    rwa [zero_smul]
#align absorbent_nhds_zero absorbent_nhds_zero

/-- The union of `{0}` with the interior of a balanced set is balanced. -/
theorem balanced_zero_union_interior (hA : Balanced 𝕜 A) :
    Balanced 𝕜 ((0 : Set E) ∪ interior A) := by
  intro a ha
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_smul_set]
    exacts [subset_union_left _ _, ⟨0, Or.inl rfl⟩]
  · rw [← image_smul, image_union]
    apply union_subset_union
    · rw [image_zero, smul_zero]
      rfl
    · calc
        a • interior A ⊆ interior (a • A) := (isOpenMap_smul₀ h).image_interior_subset A
        _ ⊆ interior A := interior_mono (hA _ ha)
#align balanced_zero_union_interior balanced_zero_union_interior

/-- The interior of a balanced set is balanced if it contains the origin. -/
theorem Balanced.interior (hA : Balanced 𝕜 A) (h : (0 : E) ∈ interior A) :
    Balanced 𝕜 (interior A) := by
  rw [← union_eq_self_of_subset_left (singleton_subset_iff.2 h)]
  exact balanced_zero_union_interior hA
#align balanced.interior Balanced.interior

theorem Balanced.closure (hA : Balanced 𝕜 A) : Balanced 𝕜 (closure A) := fun _a ha =>
  (image_closure_subset_closure_image <| continuous_id.const_smul _).trans <|
    closure_mono <| hA _ ha
#align balanced.closure Balanced.closure

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s : Set E}

theorem Absorbent.zero_mem' (hs : Absorbent 𝕜 s) : (0 : E) ∈ s := hs.zero_mem

variable [Module ℝ E] [SMulCommClass ℝ 𝕜 E]

theorem balanced_convexHull_of_balanced (hs : Balanced 𝕜 s) : Balanced 𝕜 (convexHull ℝ s) := by
  suffices Convex ℝ { x | ∀ a : 𝕜, ‖a‖ ≤ 1 → a • x ∈ convexHull ℝ s } by
    rw [balanced_iff_smul_mem] at hs ⊢
    refine' fun a ha x hx => convexHull_min _ this hx a ha
    exact fun y hy a ha => subset_convexHull ℝ s (hs ha hy)
  intro x hx y hy u v hu hv huv a ha
  simp only [smul_add, ← smul_comm]
  exact convex_convexHull ℝ s (hx a ha) (hy a ha) hu hv huv
#align balanced_convex_hull_of_balanced balanced_convexHull_of_balanced

end NontriviallyNormedField

section Real

variable [AddCommGroup E] [Module ℝ E] {s : Set E}

theorem balanced_iff_neg_mem (hs : Convex ℝ s) : Balanced ℝ s ↔ ∀ ⦃x⦄, x ∈ s → -x ∈ s := by
  refine' ⟨fun h x => h.neg_mem_iff.2, fun h a ha => smul_set_subset_iff.2 fun x hx => _⟩
  rw [Real.norm_eq_abs, abs_le] at ha
  rw [show a = -((1 - a) / 2) + (a - -1) / 2 by ring, add_smul, neg_smul, ← smul_neg]
  exact
    hs (h hx) hx (div_nonneg (sub_nonneg_of_le ha.2) zero_le_two)
      (div_nonneg (sub_nonneg_of_le ha.1) zero_le_two) (by ring)
#align balanced_iff_neg_mem balanced_iff_neg_mem

end Real

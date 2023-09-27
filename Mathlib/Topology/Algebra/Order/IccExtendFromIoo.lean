/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.Topology.Algebra.Order.MonotoneContinuity
import Mathlib.Topology.Algebra.Order.ProjIcc

/-!
# Extend the domain of f from an open interval to the closed interval

Sometimes a function `f : (a, b) → β` can be naturally extended to `[a, b]`.

## Main statements

* `StrictMonoOn.Ioo_extend_Icc` and `StrictAntiOn.Ioo_extend_Icc`:
A strictly monotone function on an open interval can be extended to be
strictly monotone on the closed interval.
-/

open OrderDual Function Set
universe u
variable {α β : Type*} {f : α → β} [DecidableEq α]

section update
variable {s : Set α} {a : α} {b : β}

/-- Modifying the value of `f` at one point does not affect its value elsewhere.​-/
theorem Function.update.EqOn (f : α → β) (ha : a ∉ s) : EqOn (update f a b) f s := by
  intro x hx
  unfold update
  simp only [eq_rec_constant, dite_eq_ite]
  have : x ≠ a := ne_of_mem_of_not_mem hx ha
  aesop

theorem Function.update.image (f : α → β) (ha : a ∉ s) :
    (update f a b) '' (s ∪ {a}) = f '' s ∪ {b} := by
  calc
    _ = (update f a b) '' s ∪ (update f a b) '' {a} := image_union (update f a b) s {a}
    _ = (update f a b) '' s ∪ {b} := by simp
    _ = f '' s ∪ {b} := by simp only [(update.EqOn f ha).image_eq]

/-- If `a` is a strict upper bound of `s`,
`b` is a strict upper bound of `f(s)`,
and `f` is strictly monotone (increasing) on `s`,
then `f` can be extended to be strictly monotone (increasing) on `s ∪ {a}`.-/
theorem StrictMonoOn.update_strict_upper_bound  [PartialOrder α] [Preorder β]
    (hf_mono : StrictMonoOn f s) (hf_mapsto : f '' s ⊆ Iio b)
    (ha : ∀ x ∈ s, x < a) :
    StrictMonoOn (update f a b) (s ∪ {a}) := by
  unfold update
  simp only [eq_rec_constant, dite_eq_ite, union_singleton]
  intro x hx y hy hxy
  simp only
  have hxa : x ≠ a := by
    by_contra' hxa
    rw [hxa] at hxy
    cases hy with
    | inl h => rw [h] at hxy; exact hxy.false
    | inr h => exact (hxy.trans (ha y h)).false
  by_cases hya : y = a
  aesop
  aesop

/-- If `a` is a strict lower bound of `s`,
`b` is a strict lower bound of `f(s)`,
and `f` is strictly antitone (decreasing) on `s`,
then `f` can be extended to be strictly antitone (decreasing) on `s ∪ {a}`.-/
theorem StrictMonoOn.update_strict_lower_bound [PartialOrder α] [Preorder β]
    (hf_mono : StrictMonoOn f s) (hf_mapsto : f '' s ⊆ Ioi b)
    (ha : ∀ x ∈ s, a < x) :
    StrictMonoOn (update f a b) (s ∪ {a}) := by
  let g : OrderDual α → OrderDual β := f
  have hg_mono : StrictMonoOn g s := strict_mono_on_dual_iff.mp hf_mono
  have := hg_mono.update_strict_upper_bound hf_mapsto ha
  exact strict_mono_on_dual_iff.mp this

end update

section StrictMonoOn
variable [PartialOrder α] [PartialOrder β] {a b : α} {c d : β}

/-- A strictly monotone (increasing) function on an open interval can be extended
to be strictly monotone (increasing) on the closed interval.-/
theorem StrictMonoOn.Ioo_extend_Icc (hf_mono : StrictMonoOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) ⊆ Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ g, StrictMonoOn g (Icc a b) ∧
    EqOn f g {a, b}ᶜ ∧
    g '' (Icc a b) = f '' (Ioo a b) ∪ {c, d} ∧
    g = update (update f a c) b d := by
  let g : α → β := update (update f a c) b d
  use g
  have ha : a ∉ Ioo a b := by simp
  have hg_mono : StrictMonoOn g (Icc a b) := by
    have ha' : Ico a b = (Ioo a b) ∪ {a} := (Ioo_union_left hab).symm
    have hf_mono' : StrictMonoOn (update f a c) (Ico a b) := by
      rw [ha']
      refine hf_mono.update_strict_lower_bound ?mapsto ?ha
      · exact hf_mapsto.trans Ioo_subset_Ioi_self
      · aesop
    have hf_mapsto' : (update f a c) '' (Ico a b) ⊆ Ico c d := by
      rw [ha', image_union]
      simp only [(update.EqOn f ha).image_eq]
      rw [← Ioo_union_left hcd]
      simp [insert_subset_insert hf_mapsto]
    have : (update f a c) '' (Ico a b) ⊆ Iio d := hf_mapsto'.trans Ico_subset_Iio_self
    have hb : ∀ x ∈ Ico a b, x < b := by simp
    have hf_mono'' := hf_mono'.update_strict_upper_bound this hb
    replace : Ico a b ∪ {b} = Icc a b := Ico_union_right hab.le
    rw [this] at hf_mono''
    exact hf_mono''
  have hg_eq : EqOn f g {a, b}ᶜ := by
    intro x hx
    unfold_let g
    unfold update
    aesop
  have hg_image : g '' Icc a b = f '' Ioo a b ∪ {c, d} := by
    unfold_let g
    have hb : b ∉ Ico a b := by simp
    rw [← Ico_union_right hab.le, update.image (update f a c) hb,
        ← Ioo_union_left hab, update.image f ha]
    have := insert_comm d c (f '' Ioo a b)
    simp [this]
  trivial

/-- A strictly antitone (decreasing) function on an open interval can be extended
to be strictly antitone (decreasing) on the closed interval.-/
theorem StrictAntiOn.Ioo_extend_Icc (hf_mono : StrictAntiOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) ⊆ Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ g, StrictAntiOn g (Icc a b) ∧
    EqOn f g {a, b}ᶜ ∧
    g '' (Icc a b) = f '' (Ioo a b) ∪ {c, d} ∧
    g = update (update f a d) b c := by
  let g : α → OrderDual β := f
  have hg_mono : StrictMonoOn g (Ioo a b) := hf_mono
  have hg_mapsto : g '' (Ioo a b) ⊆ Ioo (toDual d) (toDual c) := by aesop
  choose G hG using hg_mono.Ioo_extend_Icc hg_mapsto hab hcd
  let F : α → β := G
  use F
  constructor
  · aesop
  · constructor
    · aesop
    · constructor
      · rw [hG.2.2.1]
        have := insert_comm (toDual d) (toDual c) ((fun a ↦ f a) '' Ioo a b)
        aesop
      · aesop

end StrictMonoOn

section StrictMonoOn2
variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β] {a b : α} {c d : β}

/- TODO: The condition `StrictMonoOn f` should be weakened to `MonotoneOn f`,
but we need a different proof since `StrictMonoOn.orderIso` is used below.-/
/-- A strictly monotone (increasing) function on an open interval can be continuously extended
to the closed interval.-/
theorem StrictMonoOn.Ioo_continuous_extend_Icc (hf_increasing : StrictMonoOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) = Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ g, ContinuousOn g (Icc a b) ∧ EqOn f g {a, b}ᶜ ∧
    g '' (Icc a b) = Icc c d ∧ g = update (update f a c) b d := by
  obtain ⟨g, hg⟩ := hf_increasing.Ioo_extend_Icc hf_mapsto.subset hab hcd
  use g
  have hg_mapsto := hg.2.2.1
  rw [hf_mapsto, ← Icc_diff_Ioo_same hcd.le] at hg_mapsto
  replace hg_mapsto : g '' Icc a b = Icc c d := by
    rw [hg_mapsto, @union_diff_self]
    exact union_eq_self_of_subset_left Ioo_subset_Icc_self
  let iso := hg.1.orderIso
  have : OrderTopology (g '' (Icc a b)) := by
    rw [hg_mapsto]
    exact orderTopology_of_ordConnected
  have iso.extend.c : Continuous (IccExtend hab.le iso) :=
      continuous_IccExtend_iff.mpr iso.continuous
  set iso.extend := IccExtend hab.le iso
  let iso.val := Subtype.val ∘ iso.extend
  have iso.eq : EqOn iso.val g (Icc a b) := by
    unfold_let iso.val iso.extend
    intro x hx
    unfold IccExtend projIcc
    have : max a (min b x) = x := by aesop
    simp [this]
    exact rfl
  have iso.val.c : Continuous iso.val := continuous_induced_rng.mp iso.extend.c
  have iso.val.c_on : ContinuousOn iso.val (Icc a b) := Continuous.continuousOn iso.val.c
  have hg_c : ContinuousOn g (Icc a b) := by
    exact Iff.mpr (continuousOn_congr (id (EqOn.symm iso.eq))) iso.val.c_on
  exact ⟨hg_c, ⟨hg.2.1, ⟨hg_mapsto, hg.2.2.2⟩⟩⟩

/-- A strictly antitone (decreasing) function on an open interval can be continuously extended
to the closed interval.-/
theorem StrictAntiOn.Ioo_continuous_extend_Icc (hf_decreasing : StrictAntiOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) = Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ g, ContinuousOn g (Icc a b) ∧ EqOn f g {a, b}ᶜ ∧
    g '' (Icc a b) = Icc c d ∧ g = update (update f a d) b c := by
  let F : α → OrderDual β := f
  have hF_increasing : StrictMonoOn F (Ioo a b) := hf_decreasing
  have hF_mapsto : F '' (Ioo a b) = Ioo (toDual d) (toDual c) := by aesop
  obtain ⟨G, hG⟩ := hF_increasing.Ioo_continuous_extend_Icc hF_mapsto hab hcd
  let g : α → β := G
  use g
  aesop

end StrictMonoOn2

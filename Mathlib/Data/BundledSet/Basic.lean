import Mathlib.Data.Set.Basic

open Function

structure BundledSet (α : Type _) (p : Set α → Prop) where
  carrier : Set α
  prop : p carrier

namespace BundledSet

attribute [coe] carrier

initialize_simps_projections BundledSet

variable {p : Set α → Prop} {s t : BundledSet α p} {a b : α}

instance : CoeTC (BundledSet α p) (Set α) := ⟨carrier⟩
instance : Membership α (BundledSet α p) := ⟨(· ∈ carrier ·)⟩
instance : CoeSort (BundledSet α p) (Type _) := ⟨fun s ↦ {x // x ∈ s}⟩

@[simp] theorem mem_carrier : a ∈ s.carrier ↔ a ∈ s := Iff.rfl

@[simp, norm_cast] theorem coeSort_carrier : ((s : Set α) : Type _) = s := rfl

@[simp] theorem coe_mem (x : s) : ↑x ∈ s := x.2

theorem carrier_injective : Injective (carrier (p := p)) | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp, norm_cast]
theorem carrier_inj : s.carrier = t.carrier ↔ s = t :=
  carrier_injective.eq_iff

protected theorem ext_iff : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t := by
  rw [← carrier_inj, Set.ext_iff]; rfl

@[ext] protected theorem ext (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := BundledSet.ext_iff.2 h

instance : PartialOrder (BundledSet α p) :=
  { PartialOrder.lift carrier carrier_injective with
    le := fun s t ↦ ∀ ⦃x⦄, x ∈ s → x ∈ t
    lt := fun s t ↦ s ≤ t ∧ ¬t ≤ s }

theorem le_def : s ≤ t ↔ ∀ ⦃x⦄, x ∈ s → x ∈ t := Iff.rfl

@[simp, norm_cast] theorem carrier_subset_carrier : (s : Set α) ⊆ t ↔ s ≤ t := Iff.rfl
@[simp, norm_cast] theorem carrier_ssubset_carrier : (s : Set α) ⊂ t ↔ s < t := Iff.rfl

theorem carrier_mono : Monotone (carrier (p := p)) := fun _ _ ↦ id
theorem carrier_strictMono : StrictMono (carrier (p := p)) := fun _ _ ↦ id

theorem not_le_iff_exists : ¬s ≤ t ↔ ∃ x ∈ s, x ∉ t := Set.not_subset

theorem exists_of_lt : s < t → ∃ x ∈ t, x ∉ s := Set.exists_of_ssubset

theorem lt_iff_le_and_exists : s < t ↔ s ≤ t ∧ ∃ x ∈ t, x ∉ s := by
  rw [lt_iff_le_not_le, not_le_iff_exists]

end BundledSet

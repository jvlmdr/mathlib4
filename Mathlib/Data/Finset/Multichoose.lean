/-
Copyright (c) 2024 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Data.Multiset.Multichoose

/-!
# Finset multichoose

Describes the `Finset` of `Multiset`s of a given size obtained by selecting elements from a
`Finset` with replacement.
-/

open scoped BigOperators List

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- Finds all unique multisets of cardinality `n` formed using the elements of `s`. -/
def multichoose (n : ℕ) (s : Finset α) : Finset (Multiset α) :=
  ⟨Multiset.multichoose n s.1, Multiset.nodup_multichoose s.nodup⟩

lemma multichoose_val {n : ℕ} {s : Finset α} :
    (multichoose n s).val = Multiset.multichoose n s.val := rfl

@[simp]
lemma multichoose_zero {s : Finset α} : multichoose 0 s = {0} := by
  simp [multichoose]
  rfl

@[simp]
lemma multichoose_succ_empty {n : ℕ} : multichoose n.succ (∅ : Finset α) = ∅ := by
  simp [multichoose]

/-- The number of elements in `multichoose`. -/
theorem card_multichoose (n : ℕ) (s : Finset α) :
    (multichoose n s).card = Nat.multichoose (s.card) n := by
  simp [multichoose, Multiset.card_multichoose]

/-- Necessary and sufficient condition for a `Multiset` to be a member of `multichoose`. -/
theorem mem_multichoose_iff {n : ℕ} {s : Finset α} {t : Multiset α} :
    t ∈ multichoose n s ↔ Multiset.card t = n ∧ ∀ x ∈ t, x ∈ s := by
  simp [multichoose, Multiset.mem_multichoose_iff]

theorem card_of_mem_multichoose {n : ℕ} {s : Finset α} {t : Multiset α} (ht : t ∈ multichoose n s) :
    Multiset.card t = n := (mem_multichoose_iff.mp ht).1

theorem mem_of_mem_multichoose {n : ℕ} {s : Finset α} {t : Multiset α} (ht : t ∈ multichoose n s) :
    ∀ x ∈ t, x ∈ s := (mem_multichoose_iff.mp ht).2

theorem multichoose_succ_insert {n : ℕ} {x : α} {s : Finset α} (hx : x ∉ s) :
    multichoose n.succ (insert x s) =
    multichoose n.succ s ∪
      (multichoose n (insert x s)).map (Multiset.consRightEmbedding x).toEmbedding := by
  ext t
  simp only [multichoose, mem_union, mem_map, mem_mk]
  simp only [insert_val, Multiset.ndinsert_of_not_mem hx]
  simp [Multiset.multichoose_succ_cons]

/-- The union in `multichoose_succ_insert` is disjoint. -/
theorem disjoint_multichoose_succ_insert {n : ℕ} {x : α} {s : Finset α} (hx : x ∉ s) :
    Disjoint (multichoose n.succ s)
      ((multichoose n (insert x s)).map (Multiset.consRightEmbedding x).toEmbedding) := by
  simp only [disjoint_iff_ne, mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, RelEmbedding.coe_toEmbedding, Multiset.consRightEmbedding_apply]
  intro t hts r _ h
  simp only [h, mem_multichoose_iff, Multiset.mem_cons, forall_eq_or_imp] at hts
  exact hx hts.2.1

theorem multichoose_singleton {n : ℕ} {x : α} : multichoose n {x} = {Multiset.replicate n x} := by
  ext t
  simp [multichoose, Multiset.multichoose_singleton]

theorem multichoose_one {s : Finset α} : multichoose 1 s = s.map Multiset.singletonEmbedding := by
  ext t
  simp only [mem_multichoose_iff, mem_map, Multiset.singletonEmbedding_apply, Multiset.card_eq_one]
  refine Iff.intro ?_ ?_
  · simp only [and_imp, forall_exists_index]
    intro x ht
    simp [ht]
  · simp only [and_imp, forall_exists_index]
    intro x hxs ht
    simp [← ht, hxs]

@[simp]
lemma card_multichoose_one {s : Finset α} : card (multichoose 1 s) = card s := by
  simp [multichoose_one]

theorem multichoose_eq_empty_iff {n : ℕ} (s : Finset α) :
    multichoose n s = ∅ ↔ n ≠ 0 ∧ s = ∅ := by
  rw [← Finset.card_eq_zero]
  rw [card_multichoose]
  rw [← Finset.card_eq_zero]
  rw [and_comm]
  exact Nat.multichoose_eq_zero_iff

theorem mem_multichoose_iff_mem_powersetCard_nsmul_val {n : ℕ} {s : Finset α} {t : Multiset α} :
    t ∈ multichoose n s ↔ t ∈ (n • s.val).powersetCard n := by
  simp [mem_multichoose_iff]
  rw [and_comm, and_congr_left_iff]
  intro ht
  rw [← ht]
  simp [Multiset.le_iff_count]
  simp [Multiset.count_eq_of_nodup s.nodup]
  -- simp [apply_ite]
  refine Iff.intro ?_ ?_
  · intro h x
    by_cases hxt : x ∈ t
    · simp [h x hxt]
      exact Multiset.count_le_card x t
    · simp [hxt]
  · intro h x hxt
    by_cases hxs : x ∈ s <;> simp [hxs]
    specialize h x
    simp [hxs] at h
    exact h hxt

theorem multichoose_eq_toFinset_powersetCard_nsmul_val {n : ℕ} {s : Finset α} :
    multichoose n s = ((n • s.val).powersetCard n).toFinset := by
  ext t
  simp [-Multiset.mem_powersetCard]
  exact mem_multichoose_iff_mem_powersetCard_nsmul_val

theorem multichoose_eq_toFinset_multichoose_val {n : ℕ} {s : Finset α} :
    multichoose n s = (s.val.multichoose n).toFinset := by
  ext t
  simp [mem_multichoose_iff, Multiset.mem_multichoose_iff]

end Finset

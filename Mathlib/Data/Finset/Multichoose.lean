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

## Main definitions

- `multichoose n s` : The `Finset` of `Multiset`s of cardinality `n` obtained by selecting
  elements from `s` with replacement.

## Main results

- `card_multichoose` : The size of `multichoose n s` is `Nat.multichoose s.card n`.
- `mem_multichoose_iff` : `t ∈ multichoose n s` iff `t` has cardinality `n` and all its elements
  are in `s`.

- `multichoose_eq_toFinset_multichoose_val` is the unique elements of `Multiset.multichoose`.
- `multichoose_eq_toFinset_powersetCard_nsmul_val` : `Finset.multichoose` is the unique elements of
  `Multiset.powersetCard` with each element repeated `n` times.

-/

open scoped BigOperators List

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- Finds all unique multisets of cardinality `n` formed using the elements of `s`. -/
def multichoose (n : ℕ) (s : Finset α) : Finset (Multiset α) :=
  ⟨Multiset.multichoose n s.1, s.nodup.multichoose⟩

lemma multichoose_val {n : ℕ} {s : Finset α} :
    (multichoose n s).val = Multiset.multichoose n s.val := rfl

@[simp]
theorem multichoose_zero {s : Finset α} : multichoose 0 s = {0} := by
  rw [← val_inj]
  simp [multichoose]

@[simp]
lemma multichoose_succ_empty {n : ℕ} : multichoose n.succ (∅ : Finset α) = ∅ := by
  simp [multichoose]

/-- The number of elements in `multichoose`. -/
@[simp]
theorem card_multichoose (n : ℕ) (s : Finset α) :
    (multichoose n s).card = Nat.multichoose s.card n := by simp [multichoose]

/-- Necessary and sufficient condition for a `Multiset` to be a member of `multichoose`. -/
@[simp]
theorem mem_multichoose_iff {n : ℕ} {s : Finset α} {t : Multiset α} :
    t ∈ multichoose n s ↔ Multiset.card t = n ∧ ∀ x ∈ t, x ∈ s := by
  simp [multichoose]

@[simp]
theorem card_of_mem_multichoose {n : ℕ} {s : Finset α} {t : Multiset α} (ht : t ∈ multichoose n s) :
    Multiset.card t = n := (mem_multichoose_iff.mp ht).1

theorem mem_of_mem_multichoose {n : ℕ} {s : Finset α} {t : Multiset α} (ht : t ∈ multichoose n s) :
    ∀ x ∈ t, x ∈ s := (mem_multichoose_iff.mp ht).2

theorem multichoose_singleton {n : ℕ} {x : α} : multichoose n {x} = {Multiset.replicate n x} := by
  rw [← val_inj]
  simp [multichoose]

theorem multichoose_one {s : Finset α} : multichoose 1 s = s.map Multiset.singletonEmbedding := by
  rw [← val_inj]
  simp [multichoose]

theorem multichoose_eq_empty_iff {n : ℕ} (s : Finset α) :
    multichoose n s = ∅ ↔ n ≠ 0 ∧ s = ∅ := by
  rw [← val_inj]
  simp [multichoose]

/-- The union in `multichoose_succ_insert` is disjoint. -/
theorem disjoint_multichoose_succ_insert {n : ℕ} {x : α} {s : Finset α} (hx : x ∉ s) :
    Disjoint (multichoose n.succ s)
      ((multichoose n (insert x s)).map (Multiset.consRightEmbedding x).toEmbedding) := by
  rw [disjoint_left]
  intro t ht ht'
  simp only [mem_map, RelEmbedding.coe_toEmbedding, Multiset.consRightEmbedding_apply] at ht'
  rcases ht' with ⟨t', ht'⟩
  refine hx ?_
  rw [← ht'.2, mem_multichoose_iff] at ht
  refine ht.2 x ?_
  exact Multiset.mem_cons_self x t'

theorem multichoose_succ_insert {n : ℕ} {x : α} {s : Finset α} (hx : x ∉ s) :
    multichoose n.succ (insert x s) =
    multichoose n.succ s ∪
      (multichoose n (insert x s)).map (Multiset.consRightEmbedding x).toEmbedding := by
  rw [← val_inj, union_val]
  rw [← Multiset.add_eq_union_iff_disjoint.mpr]
  · simp [multichoose, Multiset.ndinsert_of_not_mem hx]
  · rw [disjoint_val]
    exact disjoint_multichoose_succ_insert hx

-- TODO: Monotone.

theorem mem_multichoose_iff_mem_powersetCard_nsmul_val {n : ℕ} {s : Finset α} {t : Multiset α} :
    t ∈ multichoose n s ↔ t ∈ (n • s.val).powersetCard n := by
  rw [mem_multichoose_iff, Multiset.mem_powersetCard]
  rw [and_comm, and_congr_left_iff]
  intro hn
  rw [← hn, Multiset.le_iff_count]
  simp only [Multiset.count_nsmul]
  refine Iff.intro ?_ ?_
  · intro hts x
    by_cases hxt : x ∈ t
    · refine le_trans (Multiset.count_le_card x t) ?_
      refine le_mul_of_one_le_right (Nat.zero_le _) ?_
      rw [Multiset.one_le_count_iff_mem]
      exact hts x hxt
    · simp [hxt]
  · intro hts x hxt
    specialize hts x
    by_contra hxs
    revert hxt
    rw [imp_false]
    simpa [hxs] using hts

/-- `Finset.multichoose` is the unique elements of `Multiset.multichoose`. -/
theorem multichoose_eq_toFinset_multichoose_val {n : ℕ} {s : Finset α} :
    multichoose n s = (s.val.multichoose n).toFinset := by
  ext t
  simp

/--
`Finset.multichoose` is the unique elements of `Multiset.powersetCard` with each element repeated
`n` times.
-/
theorem multichoose_eq_toFinset_powersetCard_nsmul_val {n : ℕ} {s : Finset α} :
    multichoose n s = ((n • s.val).powersetCard n).toFinset := by
  ext t
  rw [Multiset.mem_toFinset]
  exact mem_multichoose_iff_mem_powersetCard_nsmul_val

end Finset

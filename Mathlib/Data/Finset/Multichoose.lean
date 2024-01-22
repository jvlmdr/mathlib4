/-
Copyright (c) 2024 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Data.Multiset.Multichoose
import Mathlib.Data.Nat.Choose.Multinomial

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
- `pow_sum` : The multinomial theorem for a power of a sum.

- `multichoose_eq_toFinset_multichoose_val` : `Finset.multichoose` is the unique elements of
  `Multiset.multichoose`.
- `multichoose_eq_toFinset_powersetCard_nsmul_val` : `Finset.multichoose` is the unique elements of
  `Multiset.powersetCard` with each element repeated `n` times.
-/

open Function.Embedding
open scoped BigOperators List

section Definition

variable {α : Type*} [DecidableEq α]

/-- Finds all unique multisets of cardinality `n` formed using the elements of `s`. -/
def Finset.multichoose (n : ℕ) (s : Finset α) : Finset (Multiset α) :=
  ⟨Multiset.multichoose n s.1, s.nodup.multichoose⟩

lemma Finset.multichoose_val {n : ℕ} {s : Finset α} :
    (multichoose n s).val = Multiset.multichoose n s.val := rfl

theorem Multiset.toFinset_multichoose {n : ℕ} {s : Multiset α} :
    (Multiset.multichoose n s).toFinset = Finset.multichoose n s.toFinset := by
  rw [← Finset.val_inj, toFinset_val]
  rw [Finset.multichoose_val, toFinset_val]
  exact dedup_multichoose

/-- `Finset.multichoose` is the unique elements of `Multiset.multichoose`. -/
theorem Finset.multichoose_eq_toFinset_multichoose_val {n : ℕ} {s : Finset α} :
    multichoose n s = (Multiset.multichoose n s.val).toFinset := by
  rw [← val_inj, Multiset.toFinset_multichoose]
  simp

namespace Finset

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

/-- `multichoose n` is monotone with respect to the input `Finset`. -/
theorem multichoose_mono {n : ℕ} : Monotone (multichoose n (α := α)) := by
  intro s t
  simp only [le_eq_subset, ← val_le_iff, multichoose_val]
  exact fun h ↦ Multiset.multichoose_mono h

/--
`Finset.multichoose` is the unique elements of `Multiset.powersetCard` with each element repeated
`n` times.
-/
theorem multichoose_eq_toFinset_powersetCard_nsmul_val {n : ℕ} {s : Finset α} :
    multichoose n s = (Multiset.powersetCard n (n • s.val)).toFinset := by
  ext t
  rw [mem_multichoose_iff, Multiset.mem_toFinset, Multiset.mem_powersetCard]
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

-- TODO: Use `Finset.image` proofs to simplify this?
theorem multichoose_eq_biUnion_multichoose_erase {k : ℕ} {s : Finset α} {x : α} (hx : x ∈ s) :
    s.multichoose k = (range k.succ).biUnion fun m ↦
      ((s.erase x).multichoose (k - m)).map (addLeftEmbedding (Multiset.replicate m x)) := by
  ext t
  simp only [mem_biUnion, mem_range, mem_map, addLeftEmbedding_apply, Nat.lt_succ]
  simp only [mem_multichoose_iff]
  refine Iff.intro ?_ ?_
  · intro ht
    use t.count x
    rw [← ht.1]
    refine And.intro ?_ ?_
    · simp [Multiset.count_le_card]
    · use t.filter (· ≠ x)
      refine And.intro (And.intro ?_ ?_) ?_
      · exact (Multiset.card_sub_count_eq_card_filter_ne t x).symm
      · simp only [Multiset.mem_filter, mem_erase, and_imp]
        exact (fun a ha h ↦ ⟨h, ht.2 a ha⟩)
      · rw [← Multiset.filter_eq', Multiset.filter_add_not]
  · simp only [forall_exists_index, and_imp]
    intro m hm u hu_card hu_mem ht
    refine And.intro ?_ ?_
    · simp [← ht, hu_card, hm]
    · rw [← ht]
      simp only [Multiset.mem_add, Multiset.mem_replicate]
      intro a ha
      cases ha with
      | inl ha => rw [ha.2]; exact hx
      | inr ha => exact mem_of_mem_erase (hu_mem a ha)

/-! ### Bijection between multichoose and (count of one element, multichoose of rest) -/


/-- Image of count-remove on `Finset.multichoose k s` as a `Finset`. -/
def multichooseSplit (n : ℕ) (s : Finset α) (x : α) : Finset (ℕ × Multiset α) :=
  (range n.succ).biUnion fun m ↦ (multichoose (n - m) (s.erase x)).map (sectr m (Multiset α))

/--
`multichooseSplit` is a `Finset` representation of
`{q : ℕ × Multiset (Fin n) | q.1 ≤ n ∧ q.2 ∈ Finset.multichoose (n - q.1) Finset.univ}`.
-/
theorem mem_multichooseSplit_iff {n : ℕ} {s : Finset α} {x : α} {q : ℕ × Multiset α} :
    q ∈ multichooseSplit n s x ↔ q.1 ≤ n ∧ q.2 ∈ multichoose (n - q.1) (s.erase x) := by
  rcases q with ⟨m, t⟩
  simp [multichooseSplit, Nat.lt_succ]

/-- The union in `multichooseSplit` is pairwise disjoint. -/
theorem pairwiseDisjoint_multichooseSplit (n : ℕ) (s : Finset α) (x : α) :
    Set.PairwiseDisjoint ↑(range (Nat.succ n)) fun m ↦
      ((s.erase x).multichoose (n - m)).map (sectr m (Multiset α)) := by
  intro i _ j _ hij
  simp [disjoint_iff_ne, hij, -mem_multichoose_iff]

-- TODO: Can the disjoint property be used to simplify the following proofs?

/-- `fun t ↦ (t.count x, t.filter (· ≠ x))` maps `multichoose n s` to `multichooseSplit n s x`. -/
theorem prodCountFilterNe_mem_multichooseSplit {n : ℕ} {s : Finset α} {x : α} :
    ∀ t ∈ multichoose n s, (t.count x, t.filter (· ≠ x)) ∈ multichooseSplit n s x := by
  intro t ht
  rw [mem_multichoose_iff] at ht
  rcases ht with ⟨ht_card, ht_mem⟩
  rw [← ht_card]
  refine mem_multichooseSplit_iff.mpr (And.intro ?_ ?_)
  · exact Multiset.count_le_card x t
  · refine mem_multichoose_iff.mpr (And.intro ?_ ?_)
    · rw [Multiset.card_sub_count_eq_card_filter_ne]
    · simp only [Multiset.mem_filter, mem_erase, and_imp]
      intro a ha
      simp [ht_mem a ha]

/--
For `x ∈ s`, `fun (m, t) ↦ Multiset.replicate m x + t` maps `multichooseSplit n s x` to
`multichoose n s`.
-/
theorem replicateAdd_mem_multichoose {n : ℕ} {s : Finset α} {x : α} (hx : x ∈ s) :
    ∀ q ∈ multichooseSplit n s x, Multiset.replicate q.1 x + q.2 ∈ multichoose n s := by
  intro q hq
  rcases q with ⟨m, t⟩
  simp only [mem_multichooseSplit_iff, mem_multichoose_iff] at hq
  rcases hq with ⟨hm, ht_card, ht_mem⟩
  refine mem_multichoose_iff.mpr (And.intro ?_ ?_)
  · simp [ht_card, hm]
  · intro a ha
    simp only [Multiset.mem_add, Multiset.mem_replicate] at ha
    cases ha with
    | inl ha => rw [ha.2]; exact hx
    | inr ha => exact mem_of_mem_erase (ht_mem a ha)

/--
`fun (m, t) ↦ Multiset.replicate m x + t` is the left inverse of
`fun t ↦ (t.count x, t.filter (· ≠ x))`.
-/
theorem replicateAdd_countConsFilterNe_eq_self {x : α} {t : Multiset α} :
    Multiset.replicate (t.count x) x + t.filter (· ≠ x) = t := by
  simp [← Multiset.filter_eq', Multiset.filter_add_not]

/--
`fun t ↦ (t.count x, t.filter (· ≠ x))` is the left inverse of
`fun (m, t) ↦ Multiset.replicate m x + t` on `multichooseSplit n s x`.
-/
theorem countConsFilterNe_replicateAdd_eq_self {n : ℕ} {s : Finset α} {x : α} :
    ∀ q ∈ multichooseSplit n s x,
    ⟨(Multiset.replicate q.1 x + q.2).count x,
     (Multiset.replicate q.1 x + q.2).filter (· ≠ x)⟩ = q := by
  intro q
  rcases q with ⟨m, t⟩
  simp only [mem_coe, mem_multichooseSplit_iff, mem_multichoose_iff, and_imp]
  intro _ _ ht_mem
  refine Prod.mk.inj_iff.mpr (And.intro ?_ ?_)
  · rw [Multiset.count_add, Multiset.count_replicate_self]
    rw [add_right_eq_self, Multiset.count_eq_zero]
    intro hxt
    exact not_mem_erase x s (ht_mem x hxt)
  · rw [Multiset.filter_add]
    rw [Multiset.filter_eq_nil.mpr (by simp [Multiset.mem_replicate])]
    rw [Multiset.filter_eq_self.mpr (fun a ha ↦ ne_of_mem_erase (ht_mem a ha))]
    simp

/--
`multichooseSplit n s x` is the image of `multichoose n s` under
`fun t ↦ (t.count x, t.filter (· ≠ x))`.
-/
theorem image_prodCountFilterNe_multichoose {n : ℕ} {s : Finset α} {x : α} (hx : x ∈ s) :
    (multichoose n s).image (fun t ↦ (t.count x, t.filter (· ≠ x))) =
      multichooseSplit n s x := by
  ext q
  simp only [mem_image]
  refine Iff.intro ?_ ?_
  · simp only [forall_exists_index, and_imp]
    intro t ht hq
    rw [← hq]
    exact prodCountFilterNe_mem_multichooseSplit t ht
  · intro hq
    use Multiset.replicate q.1 x + q.2
    refine And.intro ?_ ?_
    · refine replicateAdd_mem_multichoose hx q hq
    · exact countConsFilterNe_replicateAdd_eq_self q hq

/--
`multichoose n s` is the image of `multichooseSplit n s x` under
`fun (m, t) ↦ Multiset.replicate m x + t`.
-/
theorem image_replicateAdd_multichooseSplit {n : ℕ} {s : Finset α} {x : α} (hx : x ∈ s) :
    (multichooseSplit n s x).image (fun q ↦ Multiset.replicate q.1 x + q.2) = multichoose n s := by
  ext t
  simp only [mem_image]
  refine Iff.intro ?_ ?_
  · simp only [forall_exists_index, and_imp]
    intro q hq ht
    rw [← ht]
    exact replicateAdd_mem_multichoose hx q hq
  · intro ht
    use (t.count x, t.filter (· ≠ x))
    refine And.intro ?_ ?_
    · exact prodCountFilterNe_mem_multichooseSplit t ht
    · simp [replicateAdd_countConsFilterNe_eq_self]

end Finset

end Definition

/-! ### Multinomial theorem -/


section Sum

/-
Note: Could not put this in `Mathlib.Algebra.BigOperators.Ring` due to circular import.
Requires `Multiset.multinomial` from `Mathlib.Data.Nat.Choose.Multinomial`.

error: build cycle detected:
  +Mathlib.Data.Nat.Choose.Multinomial:lean.precompileImports
  +Mathlib.Algebra.BigOperators.Ring:lean.precompileImports
  +Mathlib.Data.Fintype.BigOperators:lean.precompileImports
  +Mathlib.Algebra.BigOperators.Fin:lean.precompileImports
  +Mathlib.Data.Nat.Choose.Multinomial:lean.precompileImports
-/

variable {ι : Type*} [DecidableEq ι]
variable {α : Type*} [CommSemiring α]

namespace Finset

/--
[Multinomial theorem](https://en.wikipedia.org/wiki/Multinomial_theorem)
for the expansion of a power of a sum.
-/
theorem pow_sum {p : ℕ} {s : Finset ι} {f : ι → α} :
    (∑ i in s, f i) ^ p = ∑ k in s.multichoose p, k.multinomial * ∏ i in s, f i ^ k.count i := by
  induction s using Finset.induction generalizing p with
  | empty => cases p <;> simp
  | @insert a s ha ih =>
    -- Apply binomial theorem on left.
    rw [sum_insert ha, add_pow]
    -- Re-index sum on right.
    -- TODO: Could be made much more succinct by introducing e.g. `sum_nbij_comp`.
    have : ∑ k in multichoose p (insert a s), k.multinomial * ∏ i in insert a s, f i ^ k.count i =
        ∑ q in multichooseSplit p (insert a s) a, (Multiset.replicate q.1 a + q.2).multinomial *
          ∏ x in insert a s, f x ^ Multiset.count x (Multiset.replicate q.1 a + q.2) :=
      sum_nbij' (fun t ↦ (t.count a, t.filter (· ≠ a))) (fun q ↦ Multiset.replicate q.1 a + q.2)
        (prodCountFilterNe_mem_multichooseSplit)
        (replicateAdd_mem_multichoose (mem_insert_self a s))
        (fun _ _ ↦ replicateAdd_countConsFilterNe_eq_self)
        (countConsFilterNe_replicateAdd_eq_self)
        (fun _ _ ↦ by simp only [replicateAdd_countConsFilterNe_eq_self])
    rw [this]; clear this
    rw [multichooseSplit]
    rw [sum_biUnion (pairwiseDisjoint_multichooseSplit p _ a)]
    refine sum_congr rfl ?_
    simp only [mem_range, Nat.lt_succ]
    intro m hmp
    -- Apply inductive hypothesis on left then simplify inner sum on right.
    rw [ih, mul_sum, sum_mul]
    rw [sum_map, erase_insert_eq_erase, erase_eq_of_not_mem ha]
    refine sum_congr rfl ?_
    intro t ht
    -- Separate the multinomial and product terms.
    suffices : (Multiset.replicate m a + t).multinomial = p.choose m * t.multinomial ∧
        ∏ i in insert a s, f i ^ (Multiset.replicate m a + t).count i =
          f a ^ m * ∏ i in s, f i ^ t.count i
    · simp only [this, Nat.cast_mul, sectr_apply]
      ring_nf
    rw [mem_multichoose_iff] at ht
    -- `s` is a disjoint union of `t` and `{a}`.
    have hat : a ∉ t := fun h ↦ ha (ht.2 a h)
    have hs_ne : ∀ i ∈ s, i ≠ a := fun i his hia ↦ by rw [hia] at his; exact ha his
    refine And.intro ?_ ?_
    · -- Split the multinomial term.
      rw [Multiset.multinomial_filter_ne a]
      refine congrArg₂ _ ?_ ?_
      · simp [ht.1, hmp, hat]
      · rw [Multiset.filter_add]
        simp only [ne_comm (a := a), Multiset.filter_add]
        rw [Multiset.filter_eq_nil.mpr (by simp [Multiset.mem_replicate])]
        rw [Multiset.filter_eq_self.mpr (fun b hb ↦ ne_of_mem_of_not_mem hb hat)]
        rw [zero_add]
    · -- Split the product.
      rw [prod_insert ha]
      refine congrArg₂ _ ?_ (prod_congr rfl ?_)
      · simp [hat]
      · intro i hi
        simp [Multiset.count_replicate, hs_ne i hi]

end Finset

-- TODO: Move?
theorem List.finRange_map_get_cast {n : ℕ} {l : List α} (hn : n = l.length) :
    (finRange n).map (fun i ↦ l.get (i.cast hn)) = l := by
  refine Eq.trans ?_ l.finRange_map_get
  simp only [finRange, map_pmap, hn]
  refine pmap_congr _ ?_
  simp

-- theorem Multiset.sum_map_comp {κ : Type*} [DecidableEq κ] (f : κ → α) (g : ι → κ) {s : Multiset ι} :
--     Multiset.sum (s.map (f ∘ g)) =
--     Finset.sum (s.toFinset.image g) fun k ↦ Multiset.count k (s.map g) • f k := by
--   rw [← map_map, Finset.sum_multiset_map_count, toFinset_map]

#check Nat.multichoose_succ_eq
#check Multiset.multinomial_eq

-- `Multiset.multinomial m = Nat.multinomial (Multiset.toFinset m) fun a ↦ Multiset.count a m`

theorem Nat.multinomial_succ {s : Finset ι} {f : ι → ℕ} {i : ι} (hi : i ∈ s) :
    multinomial s (f + fun j ↦ if j = i then 1 else 0) * sorry =
    multinomial s f * sorry := by
  simp only [multinomial]

  sorry

theorem Nat.multinomial_succ' {s : Finset ι} {f : ι → ℕ} {i : ι} (hi : i ∈ s) :
    multinomial s (fun j ↦ if j = i then (f j).succ else f j) = sorry := by
  sorry

theorem Multiset.multinomial_cons_of_mem {x : ι} {s : Multiset ι} (hxs : x ∈ s) :
    multinomial (x ::ₘ s) =
    -- (Nat.multinomial (x ::ₘ s).toFinset fun a ↦ count a (x ::ₘ s))
    -- Nat.choose (count x (x ::ₘ s) + ∑ i in toFinset s, count i (x ::ₘ s)) (count x (x ::ₘ s)) *
    --   Nat.multinomial (toFinset s) fun a ↦ count a (x ::ₘ s)
    -- Nat.choose (f a + Finset.sum s fun (i : α) => f i) (f a) * Nat.multinomial s f := by
    -- Nat.choose (count x s + card s + 1) (count x s + 1) *
    --   Nat.multinomial (toFinset s) (card s + 1) := by
    sorry := by
  simp only [multinomial_eq, toFinset_cons]
  rw [Nat.multinomial_insert]
  simp

  sorry

  -- simp only [multinomial_eq, toFinset_cons]
  -- rw [Nat.multinomial_insert]
  -- refine congrArg₂ _ ?_ ?_

  -- sorry

  -- rw [multinomial_eq, toFinset_cons]
  -- rw [Nat.multinomial_insert]
  -- simp



theorem Multiset.multinomial_cons {x : ι} {s : Multiset ι} :
    multinomial (x ::ₘ s) =
    -- (Nat.multinomial (x ::ₘ s).toFinset fun a ↦ count a (x ::ₘ s))
    -- Nat.choose (count x (x ::ₘ s) + ∑ i in toFinset s, count i (x ::ₘ s)) (count x (x ::ₘ s)) *
    --   Nat.multinomial (toFinset s) fun a ↦ count a (x ::ₘ s)

    -- Nat.choose (f a + Finset.sum s fun (i : α) => f i) (f a) * Nat.multinomial s f := by
    Nat.choose (s.count x + card s) (s.count x) * s.multinomial := by
  simp only [multinomial_eq, toFinset_cons]
  rw [Nat.multinomial_insert]

  simp only [multinomial_eq, toFinset_cons]
  rw [Nat.multinomial_insert]
  refine congrArg₂ _ ?_ ?_

  sorry

  rw [multinomial_eq, toFinset_cons]
  rw [Nat.multinomial_insert]
  simp


  -- by_cases hx : x ∈ s
  -- · simp [hx]
  --   -- `Nat.multinomial (toFinset s) fun a ↦ count a (x ::ₘ s)`
  --   sorry
  -- · simp [hx, Nat.succ_mul]

  --   --- `(Nat.succ (∑ a in toFinset s, count a (x ::ₘ s)) * Nat.multinomial (toFinset s) fun a ↦ count a (x ::ₘ s))`
  --   -- simp only [mem_toFinset, hx, not_false_eq_true, count_cons_self, count_eq_zero_of_not_mem,
  --   --   zero_add, Nat.multinomial_insert_one]
  --   simp only [mem_toFinset, hx, not_false_eq_true, count_cons_self, count_eq_zero_of_not_mem,
  --     zero_add, Nat.multinomial_insert_one]

  --   rw [← Finset.cons_eq_insert x s.toFinset (by simp [hx])]
  --   rw [Nat.multinomial_cons]
  --   simp only [count_cons_self]
  --   rw [Nat.choose_symm_add]
  --   rw [← Nat.multichoose_succ_eq]
  --   sorry

namespace Finset

theorem multichoose_eq_piFinset_image_univ_map {n : ℕ} {s : Finset ι} :
    multichoose n s = (Fintype.piFinset (fun _ : Fin n ↦ s)).image univ.val.map := by
  ext t
  simp only [mem_multichoose_iff, mem_image, Fintype.mem_piFinset]
  refine Iff.intro ?_ ?_
  · rw [and_imp]
    intro hsn hxs
    simp only [Fin.univ_def, Multiset.coe_map]
    have hln := (t.length_toList).trans hsn
    use fun i ↦ t.toList.get (i.cast hln.symm)
    refine And.intro ?_ ?_
    · exact fun _ ↦ hxs _ (Multiset.mem_toList.mp (t.toList.get_mem _ _))
    · simp [List.finRange_map_get_cast hln.symm]
  · simp only [forall_exists_index, and_imp]
    intro f hfs hft
    simp [← hft, hfs]

-- Need bijection between `piFinset` and `multichoose × order`?

theorem count_piFinset_val_map_univ_map {n : ℕ} {s : Finset ι} {t : Multiset ι} :
    Multiset.count t ((Fintype.piFinset (fun _ : Fin n ↦ s)).val.map univ.val.map) =
    t.multinomial := by
  induction t using Multiset.induction generalizing n s with
  | empty =>
    simp
    sorry
  | @cons x t ih =>
    simp
    sorry

theorem pow_sum' {p : ℕ} {s : Finset ι} {f : ι → α} :
    (∑ i in s, f i) ^ p = ∑ k in s.multichoose p, k.multinomial * (k.map f).prod := by
  conv => lhs; rw [← card_fin p]
  rw [← prod_const, prod_univ_sum]
  simp only [prod_eq_multiset_prod]
  simp only [← Function.comp_def f, ← Multiset.map_map]
  rw [sum_eq_multiset_sum]
  simp only [← Function.comp_apply (f := Multiset.prod) (g := Multiset.map f)]
  simp only [← Function.comp_def (f := Multiset.prod ∘ Multiset.map f)]
  rw [← Multiset.map_map]
  rw [sum_multiset_map_count, Multiset.toFinset_map, val_toFinset]
  simp only [count_piFinset_val_map_univ_map]
  rw [multichoose_eq_piFinset_image_univ_map]
  simp

end Finset

end Sum

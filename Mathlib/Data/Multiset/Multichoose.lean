/-
Copyright (c) 2024 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.List.Multichoose
import Mathlib.Data.Multiset.Basic

/-!
# Multichoose for multisets

Describes the `Multiset` of `Multiset`s of a given size obtained by selecting elements from a
`Multiset` with replacement.
Elements with multiplicity greater than one can be selected multiple times.
Compared to `List.multichoose`, contains the same number of elements but disregards the order of
elements in the output.

## Main definitions

- `multichoose` : Returns a `Multiset` of `Multiset`s of length `n`, taken with replacement.

## Main results

- `card_multichoose` : The cardinality of `multichoose` matches `Nat.multichoose`.
- `mem_multichoose_iff` : A `Multiset` belongs to `multichoose` iff its cardinality is `n` and all
  its elements appear in the input.
- `count_multichoose_card` : The multiplicity of a `Multiset` in `multichoose` is a product of
  `Nat.multichoose` using the multiplicity of its elements.
- `multichoose_mono` : `multichoose` is monotone in its input `Multiset`.
- `multichoose_le_powersetCard_nsmul` : `multichoose n s` is a subset of `powersetCard n (n • s)`.

## Implementation notes

Follows `Multiset.powersetCardAux` in using an auxiliary definition to then define quotient type.
-/

open scoped BigOperators List

variable {α : Type*} [DecidableEq α]

namespace Multiset

/-!
### Auxiliary definition

Before defining `multichoose` as a quotient type, it is necessary to first show that it is a valid
function on the equivalence class of permutations.
-/

section Aux

/-- Helper for `multichoose` that maps a list to a list. -/
def multichooseAux (n : ℕ) (l : List α) : List (Multiset α) := (l.multichoose n).map (↑)

@[simp]
theorem multichooseAux_zero {l : List α} : multichooseAux 0 l = [{}] := by simp [multichooseAux]

@[simp]
theorem multichooseAux_succ_nil {n : ℕ} : multichooseAux n.succ ([] : List α) = [] := rfl

@[simp]
lemma multichooseAux_succ_cons {n : ℕ} {x : α} {l : List α} :
    multichooseAux n.succ (x :: l) =
    multichooseAux (n + 1) l ++ List.map (cons x) (multichooseAux n (x :: l)) := by
  simp [multichooseAux, List.map_eq_map_iff]

theorem mem_multichooseAux_iff {n : ℕ} {l : List α} {t : Multiset α} :
    t ∈ multichooseAux n l ↔ card t = n ∧ ∀ x ∈ t, x ∈ l :=
  Quotient.inductionOn t fun t ↦ by simp [multichooseAux, List.exists_perm_mem_multichoose_iff]

theorem multichooseAux_cons_eq_join {n : ℕ} {x : α} {l : List α} :
    multichooseAux n (x :: l) = List.join ((List.range n.succ).map
      fun k ↦ (multichooseAux (n - k) l).map (replicate k x + ·)) := by
  induction n generalizing x l with
  | zero => simp
  | succ n ihn =>
    rw [List.range_succ_eq_map, List.map_cons, List.join_cons]
    simp [ihn, Function.comp_def]

-- For use with `Quotient.sound` in `multichoose`.
theorem multichooseAux_perm {n : ℕ} {l₁ l₂ : List α} (hl : l₁ ~ l₂) :
    multichooseAux n l₁ ~ multichooseAux n l₂ := by
  induction hl generalizing n with
  | nil => simp
  | @cons x l₁ l₂ hl ih =>
    induction n generalizing l₁ l₂ with
    | zero => simp
    | succ n ihn =>
      rw [multichooseAux_succ_cons, multichooseAux_succ_cons]
      exact ih.append ((ihn hl ih).map (cons x))
  | @swap x y l =>
    simp only [multichooseAux_cons_eq_join, List.map_join, List.map_map]
    rw [List.perm_iff_count]
    intro t
    simp only [Function.comp_def, List.map_map, List.count_join]
    -- Convert to `Finset.sum` and reorder.
    simp only [← List.sum_toFinset _ (List.nodup_range _), List.toFinset_range]
    rw [Finset.sum_comm' (t' := Finset.range n.succ) (s' := fun k ↦ Finset.range (n - k).succ)]
    · simp only [← add_assoc]
      simp [add_comm (replicate _ y), Nat.sub_sub, Nat.add_comm]
    · intro i j
      simp only [Finset.mem_range, Nat.lt_succ]
      -- In both cases, `i + j ≤ n`.
      have {i j : ℕ} : i + j ≤ n ↔ i ≤ n ∧ j ≤ n - i
      · refine Iff.intro ?_ ?_
        · exact fun hij ↦ ⟨le_trans (Nat.le_add_right i j) hij, Nat.le_sub_of_add_le' hij⟩
        · exact fun hi ↦ (Nat.le_sub_iff_add_le' hi.1).mp hi.2
      rw [← this, and_comm, ← this, add_comm]
  | @trans l₁ l₂ l₃ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Aux

/-! ### Main definition -/

/--
The `Multiset` of `Multiset`s obtained by choosing `n` elements from a `Multiset` with replacement.
-/
def multichoose (n : ℕ) (s : Multiset α) : Multiset (Multiset α) :=
  Quotient.liftOn s
    (fun l ↦ multichooseAux n l)
    (fun _ _ h ↦ Quotient.sound (multichooseAux_perm h))

theorem multichoose_coe' (n : ℕ) (l : List α) :
    multichoose n (↑l : Multiset α) = ↑(multichooseAux n l) := rfl

theorem multichoose_coe (n : ℕ) (l : List α) :
    multichoose n (↑l : Multiset α) = ↑(List.map (↑) (List.multichoose n l) : List (Multiset α)) :=
  rfl

@[simp]
theorem multichoose_succ_zero {n : ℕ} : multichoose n.succ (0 : Multiset α) = 0 := by
  generalize hs : (0 : Multiset α) = s
  symm at hs
  revert hs
  refine Quotient.inductionOn s ?_
  simp [multichoose_coe']

@[simp]
theorem multichoose_succ_cons {n : ℕ} {x : α} {s : Multiset α} :
    multichoose n.succ (x ::ₘ s) =
    multichoose n.succ s + (multichoose n (x ::ₘ s)).map (cons x) :=
  Quotient.inductionOn s fun l ↦ by simp [multichoose_coe']

@[simp]
theorem mem_multichoose_iff {n : ℕ} {s : Multiset α} {t : Multiset α} :
    t ∈ multichoose n s ↔ card t = n ∧ ∀ x ∈ t, x ∈ s :=
  Quotient.inductionOn s fun l ↦ by simp [multichoose_coe', mem_multichooseAux_iff]

@[simp]
theorem multichoose_zero {s : Multiset α} : multichoose 0 s = {0} :=
  Quotient.inductionOn s fun l ↦ by simp [multichoose_coe']

@[simp]
theorem multichoose_eq_zero_iff {n : ℕ} {s : Multiset α} :
    multichoose n s = 0 ↔ n ≠ 0 ∧ s = 0 := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    induction s using Multiset.induction with
    | empty => simp
    | @cons x s _ => simp [ih]

@[simp]
theorem multichoose_singleton {n : ℕ} {x : α} : multichoose n {x} = {replicate n x} := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← cons_zero x, multichoose_succ_cons]
    simp [ih]

@[simp]
theorem multichoose_one {s : Multiset α} : multichoose 1 s = s.map ({·}) :=
  Quotient.inductionOn s fun l ↦ by
    simp [multichoose_coe', multichooseAux, List.map_reverse, Function.comp_def]

theorem Nodup.multichooseAux {n : ℕ} {l : List α} (hl : List.Nodup l) :
    List.Nodup (multichooseAux n l) := by
  rw [Multiset.multichooseAux, List.nodup_map_iff_inj_on hl.multichoose]
  intro x hx y hy
  simp [List.perm_mem_multichoose_iff_eq_of_nodup hl hx hy]

/-- If the input contains no duplicates, then neither does `multichoose`. -/
theorem Nodup.multichoose {n : ℕ} {s : Multiset α} : Nodup s → Nodup (multichoose n s) :=
  Quotient.inductionOn s fun l hl ↦ by simp [multichoose_coe', multichooseAux hl]

theorem dedup_multichoose {n : ℕ} {s : Multiset α} :
    dedup (multichoose n s) = multichoose n (dedup s) := by
  rw [Nodup.ext]
  · simp
  · exact nodup_dedup (multichoose n s)
  · exact (nodup_dedup s).multichoose

theorem multichoose_cons_eq_sum {n : ℕ} {x : α} {s : Multiset α} :
    multichoose n (x ::ₘ s) =
    (Finset.range n.succ).sum fun k ↦ (multichoose (n - k) s).map (replicate k x + ·) :=
  Quotient.inductionOn s fun l ↦ by
    simp [multichoose_coe', multichooseAux_cons_eq_join, ← coe_join, join,
      ← List.sum_toFinset _ (List.nodup_range _)]

theorem count_multichoose_cons_of_not_mem {n : ℕ} {x : α} {s t : Multiset α} (hx : x ∉ t) :
    count t (multichoose n (x ::ₘ s)) = count t (multichoose n s) := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [multichoose_succ_cons, count_add, add_right_eq_self, count_eq_zero, mem_map,
      not_exists, not_and]
    intro u _ ht
    refine hx ?_
    simp [← ht]

theorem count_multichoose_succ_cons_of_mem {n : ℕ} {x : α} {s t : Multiset α} (hx : x ∈ t) :
    count t (multichoose n.succ (x ::ₘ s)) =
    count t (multichoose n.succ s) + count (t.erase x) (multichoose n (x ::ₘ s)) := by
  simp only [multichoose_succ_cons, count_add, add_right_inj]
  conv => lhs; rw [← cons_erase hx]
  exact count_map_eq_count' _ _ cons_injective_right _

theorem count_cons_multichoose_succ_cons_same {n : ℕ} {x : α} {s t : Multiset α} :
    count (x ::ₘ t) (multichoose n.succ (x ::ₘ s)) =
    count (x ::ₘ t) (multichoose n.succ s) + count t (multichoose n (x ::ₘ s)) := by
  rw [count_multichoose_succ_cons_of_mem (mem_cons_self x t), erase_cons_head]

@[simp]
theorem count_multichoose_card {s t : Multiset α} :
    (multichoose (card t) s).count t =
    ∏ x in toFinset t, Nat.multichoose (s.count x) (t.count x) := by
  -- Decouple `card t` from `t` to simplify predicate in inductive hypotheses.
  -- TODO: Is there a better choice of `generalizing`?
  generalize hn : card t = n
  induction n generalizing t s with
  | zero => rw [card_eq_zero] at hn; simp [hn]
  | succ n ihn =>
    induction s using Multiset.induction generalizing t with
    | empty =>
      replace hn : ∃ x, x ∈ t := by rw [← card_pos_iff_exists_mem]; rw [hn]; exact Nat.succ_pos n
      rcases hn with ⟨x, hx⟩
      simp [Finset.prod_eq_zero (mem_toFinset.mpr hx), hx]
    | @cons y s ihs =>
      by_cases hyt : y ∈ t
      · have ht' : ∃ t', y ::ₘ t' = t := ⟨t.erase y, cons_erase hyt⟩
        rcases ht' with ⟨t', ht'⟩
        rw [← ht'] at hn ⊢
        -- Split `y` term from rhs product.
        rw [toFinset_cons, ← Finset.prod_erase_mul _ _ (Finset.mem_insert_self y _)]
        simp only [Finset.erase_insert_eq_erase, count_cons_self]
        rw [Nat.multichoose_succ_succ, mul_add]
        rw [count_cons_multichoose_succ_cons_same]
        refine congrArg₂ _ ?_ ?_
        · rw [ihs hn]
          -- Split `y` term from lhs product.
          rw [toFinset_cons, ← Finset.prod_erase_mul _ _ (Finset.mem_insert_self y _)]
          refine congrArg₂ _ ?_ (by simp)
          refine Finset.prod_congr (by simp) ?_
          intro x hx
          simp [Finset.ne_of_mem_erase hx]
        · rw [ihn (by simpa using hn)]
          -- There may or may not be a `y` term in the lhs product.
          by_cases hyt' : y ∈ t'
          · rw [← Finset.prod_erase_mul _ _ (mem_toFinset.mpr hyt')]
            refine congrArg₂ _ ?_ (by simp)
            refine Finset.prod_congr rfl ?_
            intro x hx
            simp [Finset.ne_of_mem_erase hx]
          · rw [count_eq_zero_of_not_mem hyt', Nat.multichoose_zero_right, mul_one]
            refine Finset.prod_congr (by simp [hyt']) ?_
            intro x hx
            simp [Finset.ne_of_mem_erase hx]
      · rw [count_multichoose_cons_of_not_mem hyt]
        rw [ihs hn]
        refine Finset.prod_congr rfl ?_
        intro x hx
        have hxy : x ≠ y := fun hxy ↦ hyt (by rw [← hxy]; exact mem_dedup.mp hx)
        simp [hxy]

lemma count_multichoose_of_card_ne {n : ℕ} {s t : Multiset α} (hn : card t ≠ n) :
    (multichoose n s).count t = 0 := by simp [hn]

theorem count_multichoose {n : ℕ} {s t : Multiset α} :
    (multichoose n s).count t =
    if card t = n then ∏ x in toFinset t, Nat.multichoose (s.count x) (t.count x) else 0 := by
  by_cases hn : card t = n
  · rw [← hn, count_multichoose_card]; simp
  · simp [hn]

@[simp]
theorem card_multichoose {n : ℕ} {s : Multiset α} :
    card (multichoose n s) = Nat.multichoose (card s) n :=
  Quotient.inductionOn s fun l ↦ by
    simp [multichoose_coe', multichooseAux, List.length_multichoose]

/-- Given two multisets with `s ≤ t`, we have `multichoose n s ≤ multichoose n t`. -/
theorem multichoose_mono {n : ℕ} : Monotone (multichoose n (α := α)) := by
  intro s t
  simp only [le_iff_count]
  intro h u
  by_cases hn : card u = n
  · rw [← hn]
    simp only [count_multichoose_card]
    exact Finset.prod_le_prod (by simp) fun y _ ↦ Nat.multichoose_le_multichoose (count y u) (h y)
  · simp [count_multichoose_of_card_ne hn]

/-- `multichoose n` is a subset of `powersetCard` with all inputs repeated `n` times. -/
theorem multichoose_le_powersetCard_nsmul (n : ℕ) (s : Multiset α) :
    multichoose n s ≤ powersetCard n (n • s) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [le_iff_count]
    intro t
    by_cases hn : card t = n.succ
    · rw [← hn, count_multichoose_card, count_powersetCard_card]
      refine Finset.prod_le_prod (by simp) ?_
      intro x hx
      rw [hn]
      rw [count_nsmul]
      cases count x s with
      | zero =>
        rw [mem_toFinset, ← count_ne_zero] at hx
        rw [Nat.multichoose_zero_eq_zero_of_ne hx]
        exact Nat.zero_le _
      | succ m =>
        rw [Nat.multichoose_succ_eq]
        refine Nat.choose_le_choose _ ?_
        rw [add_comm]
        rw [Nat.succ_mul, Nat.mul_succ]
        rw [Nat.add_succ, ← Nat.succ_add]
        refine Nat.add_le_add_right ?_ m
        refine le_trans (count_le_card x t) ?_
        rw [hn]
        exact Nat.succ_le_succ (Nat.le_add_left n (n * m))
    · simp [hn]

/-- `multichoose n` is a subset of `powerset` with all inputs repeated `n` times. -/
theorem multichoose_le_powerset_nsmul {n : ℕ} {s : Multiset α} :
    multichoose n s ≤ powerset (n • s) :=
  le_trans (multichoose_le_powersetCard_nsmul n s) (powersetCard_le_powerset n (n • s))

variable {n : ℕ} {s : Multiset α}

#check Fintype.piFinset (fun _ : Fin n ↦ s.toFinset)

#check pi (range n) (fun _ ↦ s)

theorem multichoose_le_piFinset {n : ℕ} {s : Multiset α} :
    multichoose n s ≤ (pi (toFinset s) fun _ ↦ Finset.range (n + 1)).val := by
  rw [le_iff_count]
  intro t
  by_cases hn : card t = n
  · rw [← hn, count_multichoose_card]
    refine Finset.prod_le_prod (by simp) ?_
    intro x hx
    rw [Finset.mem_piFinset] at hx
    rw [Finset.mem_range]
    rw [hn]
    exact Nat.multichoose_le_multichoose (count x t) (hx x (mem_toFinset.mpr hx))
  · simp [count_multichoose_of_card_ne hn]

end Multiset

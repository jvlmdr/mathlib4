/-
Copyright (c) 2024 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Basic

/-!
# List multichoose

Describes the lists of a given length obtained by taking sublists with replacement.
-/

namespace List

variable {α β : Type*}

/--
Finds all lists of length `n` formed using the elements of `l` in order, with replacement.
Similar to `List.sublistsLen` and `Multiset.powersetCard` but with replacement.
Supports the definition of `Finset.multichoose`.

For comparison to `List.sublistsLen`:
```
List.multichoose 2 [0, 1] = [[1, 1], [0, 1], [0, 0]]
List.sublistsLen 2 [0, 1] = [[0, 1]]
List.sublistsLen 2 [0, 0, 1, 1] = [[1, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 0]]
```
For comparison to `Multiset.powersetCard`:
```
List.count [0, 0] (List.multichoose 2 [0, 0, 0]) = 6
Multiset.count (Multiset.ofList [0, 0]) (Multiset.powersetCard 2 ↑[0, 0, 0]) = 3
Multiset.count (Multiset.ofList [0, 0]) (Multiset.powersetCard 2 (2 • ↑[0, 0, 0])) = 15
```
-/
def multichoose : ℕ → List α → List (List α)
  | Nat.zero, _ => [[]]
  | Nat.succ _, [] => []
  | Nat.succ n, x :: l => multichoose (n + 1) l ++ map (cons x) (multichoose n (x :: l))

@[simp]
theorem multichoose_zero {l : List α} : multichoose 0 l = [[]] := by rw [multichoose]

@[simp]
theorem multichoose_succ_nil {n : ℕ} : multichoose n.succ ([] : List α) = [] := rfl

@[simp]
theorem multichoose_succ_cons {n : ℕ} {x : α} {l : List α} :
    multichoose n.succ (x :: l) =
    multichoose n.succ l ++ map (cons x) (multichoose n (x :: l)) := by
  rw [multichoose]

/-- Multichoose is empty iff `n` is non-zero and the list is empty. -/
@[simp]
theorem multichoose_eq_nil {n : ℕ} {l : List α} :
    multichoose n l = [] ↔ n ≠ 0 ∧ l = [] := by
  cases n <;> cases l <;> simp

@[simp]
theorem multichoose_ne_nil {n : ℕ} {l : List α} :
    multichoose n l ≠ [] ↔ n = 0 ∨ l ≠ [] := by
  cases n <;> simp

@[simp]
theorem mem_multichoose_nil {n : ℕ} {t : List α} :
    t ∈ multichoose n ([] : List α) ↔ n = 0 ∧ t = [] := by
  cases n <;> simp

@[simp]
theorem multichoose_nil_of_ne {n : ℕ} (hn : n ≠ 0) : multichoose n ([] : List α) = [] := by
  simp [hn]

@[simp]
theorem multichoose_nil_of_pos {n : ℕ} (hn : 0 < n) : multichoose n ([] : List α) = [] :=
  multichoose_nil_of_ne (Nat.pos_iff_ne_zero.mp hn)

@[simp]
theorem multichoose_singleton {n : ℕ} {x : α} : multichoose n [x] = [replicate n x] := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

theorem multichoose_one {l : List α} : multichoose 1 l = map (fun x => [x]) (reverse l) := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

/-- The number of elements in multichoose is equal to `Nat.multichoose`. -/
theorem length_multichoose {n : ℕ} {l : List α} :
    length (multichoose n l) = Nat.multichoose l.length n := by
  induction n generalizing l with
  | zero => simp
  | succ n ihn =>
    induction l with
    | nil => simp
    | cons x l ihl => simp [Nat.multichoose_succ_succ, ihn, ihl]

theorem mem_multichoose_succ_cons {n : ℕ} {x : α} {l : List α} {t : List α} :
    t ∈ multichoose n.succ (x :: l) ↔
    t ∈ multichoose n.succ l ∨ (∃ s ∈ multichoose n (x :: l), t = x :: s) := by
  simp [eq_comm]

theorem cons_mem_multichoose_succ_cons {n : ℕ} {x a : α} {l t : List α} :
    a :: t ∈ multichoose n.succ (x :: l) ↔
    a :: t ∈ multichoose n.succ l ∨ (a = x ∧ t ∈ multichoose n (x :: l)) := by
  rw [and_comm, eq_comm]
  simp

/-- All lists in `multichoose` have length `n`. -/
theorem length_of_mem_multichoose {n : ℕ} {l t : List α} (ht : t ∈ multichoose n l) :
    t.length = n := by
  induction n generalizing t l with
  | zero => rw [multichoose_zero, mem_singleton] at ht; simp [ht]
  | succ n ihn =>
    induction l with
    | nil => contradiction
    | cons x l ihl =>
      rw [mem_multichoose_succ_cons] at ht
      cases ht with
      | inl ht => exact ihl ht
      | inr ht =>
        rcases ht with ⟨s, hs, ht⟩
        simp [ht, ihn hs]

/-- All lists in `multichoose` are composed of elements from the original list. -/
theorem mem_of_mem_multichoose {n : ℕ} {l t : List α} (ht : t ∈ multichoose n l) :
    ∀ u ∈ t, u ∈ l := by
  induction n generalizing t l with
  | zero => rw [multichoose_zero, mem_singleton] at ht; simp [ht]
  | succ n ihn =>
    induction l with
    | nil => contradiction
    | cons a l ihl =>
      intro r hr
      rw [mem_multichoose_succ_cons] at ht
      cases ht with
      | inl ht => simp [ihl ht r hr]
      | inr ht =>
        rcases ht with ⟨s, hs, ht⟩
        rw [ht, mem_cons] at hr
        cases hr with
        | inl hr => simp [hr]
        | inr hr => exact ihn hs r hr

/-- The `multichoose` of a `Sublist` is a `Sublist` of `multichoose`. -/
theorem multichoose_sublist_multichoose {n : ℕ} {l₁ l₂ : List α} (hl : l₁ <+ l₂) :
    multichoose n l₁ <+ multichoose n l₂ := by
  induction n generalizing l₁ l₂ with
  | zero => simp
  | succ n ihn =>
    induction hl with
    | slnil => simp
    | @cons l₁ l₂ x _ ih => exact ih.trans (by simp)
    | @cons₂ l₁ l₂ x hl ih =>
      simp only [multichoose_succ_cons]
      exact ih.append ((ihn (hl.cons₂ x)).map (cons x))

/-- If the list of elements contains no duplicates, then `multichoose` contains no duplicates. -/
theorem nodup_multichoose {n : ℕ} {l : List α} (hl : Nodup l) : Nodup (multichoose n l) := by
  induction n generalizing l with
  | zero => simp
  | succ n ihn =>
    induction l with
    | nil => simp
    | cons x l ihl =>
      rw [multichoose_succ_cons]
      specialize ihn hl
      rw [nodup_cons] at hl
      specialize ihl hl.2
      refine Nodup.append ihl (ihn.map cons_injective) ?_
      have hx {t} : x :: t ∉ multichoose n.succ l :=
        fun ht ↦ hl.1 (mem_of_mem_multichoose ht x (mem_cons_self x t))
      simp [disjoint_right, hx]

/-- If a list has no duplicates, then two lists in `multichoose` are a permutation iff equal. -/
theorem perm_mem_multichoose_iff_eq_of_nodup [DecidableEq α] {n : ℕ} {l : List α} (hl : Nodup l)
    {t s : List α} (ht : t ∈ multichoose n l) (hs : s ∈ multichoose n l) :
    t ~ s ↔ t = s := by
  induction n generalizing s t l with
  | zero => simp only [multichoose_zero, mem_singleton] at ht hs; simp [ht, hs]
  | succ n ihn =>
    induction l with
    | nil => contradiction
    | cons x l ihl =>
      specialize @ihn _ hl
      rw [nodup_cons] at hl
      specialize ihl hl.2
      cases t with
      | nil => rw [nil_perm, eq_comm]
      | cons b bs =>
        cases s with
        | nil => rw [perm_nil]
        | cons c cs =>
          -- Must consider four cases:
          -- (1) `t` and `s` both use `x` (induction on `n`)
          -- (2) `t` and `s` both use only `l` (induction on `l`)
          -- (3,4) only one of `t` and `s` uses `x` (not equal)
          simp only [mem_multichoose_succ_cons, cons.injEq, exists_eq_right_right'] at ht hs
          cases ht with
          | inr ht =>
            cases hs with
            | inr hs =>
              -- (1) `t` and `s` both use `x` (induction on `n`)
              simp [ht.2, hs.2, ihn ht.1 hs.1]
            | inl hs =>
              -- (3,4) only one of `t` and `s` uses `x` (not equal)
              rw [ht.2]
              replace hs := mem_of_mem_multichoose hs
              simp only [mem_cons, forall_eq_or_imp] at hs
              have hc : x ≠ c := fun hx => by rw [← hx] at hs; exact hl.1 hs.1
              have hcs : x ∉ cs := fun hx => hl.1 (hs.2 x hx)
              simp [cons_perm_iff_perm_erase, hc, hcs]
          | inl ht =>
            cases hs with
            | inl hs =>
              -- (2) `t` and `s` both use only `l` (induction on `l`)
              exact ihl ht hs
            | inr hs =>
              -- (3,4) only one of `t` and `s` uses `x` (not equal)
              rw [hs.2]
              replace ht := mem_of_mem_multichoose ht
              simp only [mem_cons, forall_eq_or_imp] at ht
              have hb : x ≠ b := fun hx => by rw [← hx] at ht; exact hl.1 ht.1
              have hbs : x ∉ bs := fun hx => hl.1 (ht.2 x hx)
              rw [perm_comm, eq_comm]
              simp [cons_perm_iff_perm_erase, hb, hbs]

/-- Any list containing `n` elements from `l` has a permutation in `multichoose`. -/
theorem exists_perm_mem_multichoose [DecidableEq α] {n : ℕ} {l : List α} {t : List α}
    (ht_len : t.length = n) (ht_mem : ∀ x ∈ t, x ∈ l) :
    ∃ s ∈ multichoose n l, s ~ t := by
  induction n generalizing t l with
  | zero => simpa [length_eq_zero] using ht_len
  | succ n ihn =>
    induction l with
    | nil =>
      exfalso
      refine ne_nil_of_length_eq_succ ht_len ?_
      simpa [eq_nil_iff_forall_not_mem] using ht_mem
    | cons x l ihl =>
      -- Possible cases:
      -- 1. If `x ∉ t`, then we must use induction on `l`.
      -- 2. If `x ∈ t` and `x ∉ l`, then we must use induction on `n`.
      -- 3. If `x ∈ t` and `x ∈ l`, then we can use either inductive hypothesis.
      by_cases hxt : x ∈ t
      · -- 2. If `x ∈ t` and `x ∉ l`, then we must use induction on `n`.
        -- 3. If `x ∈ t` and `x ∈ l`, then we can use either inductive hypothesis.
        specialize ihn (t := t.erase x) (l := x :: l) ?_ ?_
        · simp [hxt, ht_len]
        · exact fun v hv ↦ ht_mem v (mem_of_mem_erase hv)
        rcases ihn with ⟨s, hs⟩
        use x :: s
        refine And.intro ?_ ?_
        · simp [cons_mem_multichoose_succ_cons, hs.1]
        · exact (hs.2.cons x).trans (perm_cons_erase hxt).symm
      · -- 1. If `x ∉ t`, then we must use induction on `l`.
        specialize ihl ?_
        · intro v hvt
          have hvl := mem_cons.mp (ht_mem v hvt)
          cases hvl with
          | inl hvx => exfalso; rw [hvx] at hvt; exact hxt hvt
          | inr hvl => exact hvl
        rcases ihl with ⟨s, hs⟩
        use s
        simp [mem_multichoose_succ_cons, hs]

/-- Necessary and sufficient condition for a list to have a permutation in `multichoose`. -/
theorem exists_perm_mem_multichoose_iff [DecidableEq α] {n : ℕ} {l : List α} {t : List α} :
    (∃ s ∈ multichoose n l, s ~ t) ↔ t.length = n ∧ ∀ x ∈ t, x ∈ l := by
  refine Iff.intro ?_ ?_
  · intro h
    rcases h with ⟨s, hs, hst⟩
    exact And.intro (hst.length_eq.symm.trans (length_of_mem_multichoose hs))
      (fun x hx ↦ mem_of_mem_multichoose hs x (hst.mem_iff.mpr hx))
  · exact fun h ↦ exists_perm_mem_multichoose h.1 h.2

/-- The `multichoose` list is a sublist of `sublistsLen n` with all elements repeated `n` times. -/
theorem multichoose_sublist_sublistsLen_join_map_replicate' {n : ℕ} {l : List α} :
    multichoose n l <+ sublistsLen n (l.map (replicate n)).join := by
  induction n generalizing l with
  | zero => simp
  | succ n ihn =>
    induction l with
    | nil => simp
    | cons x l ihl =>
      simp only [join, replicate, cons_append]
      rw [multichoose_succ_cons, sublistsLen_succ_cons]
      refine Sublist.append ?_ ?_
      · refine ihl.trans (sublistsLen_sublist_of_sublist n.succ ?_)
        simp
      · refine Sublist.map (cons x) ?_
        refine ihn.trans (sublistsLen_sublist_of_sublist n ?_)
        simp [Sublist.join_map]

end List

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

Describes the lists of a fixed length obtained by taking sublists with replacement.
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
  | Nat.succ n, x :: xs => List.append
      (multichoose (n + 1) xs)
      (map (cons x) (multichoose n (x :: xs)))  -- Order these to match `List.sublists`.

@[simp]
lemma multichoose_zero {l : List α} : multichoose 0 l = [[]] := by rw [multichoose]

@[simp]
lemma multichoose_succ_nil {n : ℕ} : multichoose n.succ ([] : List α) = [] := rfl

lemma multichoose_succ_cons {n : ℕ} {x : α} {xs : List α} :
    multichoose n.succ (x :: xs) = List.append
      (multichoose (n + 1) xs)
      (map (cons x) (multichoose n (x :: xs))) := by
  rw [multichoose]

@[simp]
lemma multichoose_nil {n : ℕ} (hn : n ≠ 0) :
    multichoose n ([] : List α) = [] := by
  cases n with
  | zero => contradiction
  | succ n => rfl

@[simp]
lemma mem_multichoose_nil {n : ℕ} {t : List α} :
    t ∈ multichoose n ([] : List α) ↔ n = 0 ∧ t = [] := by
  cases n <;> simp

@[simp]
lemma multichoose_singleton {n : ℕ} {x : α} : multichoose n [x] = [replicate n x] := by
  induction n with
  | zero => simp
  | succ n ih => simp [multichoose_succ_cons, ih]

theorem multichoose_one {l : List α} : multichoose 1 l = map (fun x => [x]) (reverse l) := by
  induction l with
  | nil => simp
  | cons x xs ihl => simp [multichoose_succ_cons, ihl]

/-- Multichoose is empty iff `n` is non-zero and the list is empty. -/
@[simp]
theorem multichoose_eq_empty {n : ℕ} {l : List α} :
    multichoose n l = [] ↔ n ≠ 0 ∧ l = [] := by
  induction n with
  | zero => simp
  | succ n ihn =>
    simp
    cases l with
    | nil => simp
    | cons x xs => simp [multichoose_succ_cons, ihn]

/-- The number of elements in multichoose is equal to `Nat.multichoose`. -/
theorem length_multichoose {n : ℕ} {l : List α} :
    length (multichoose n l) = Nat.multichoose l.length n := by
  induction n generalizing l with
  | zero => simp
  | succ n ihn =>
    induction l with
    | nil => simp
    | cons x xs ihl =>
      simp [multichoose_succ_cons, Nat.multichoose_succ_succ]
      simp [ihn, ihl]

lemma mem_multichoose_succ_cons {n : ℕ} {x : α} {xs : List α} {t : List α} :
    t ∈ multichoose n.succ (x :: xs) ↔
    t ∈ multichoose n.succ xs ∨ (∃ s ∈ multichoose n (x :: xs), t = x :: s) := by
  simp [multichoose_succ_cons]
  simp [eq_comm]

lemma cons_mem_multichoose_succ_cons {n : ℕ} {x y : α} {xs ys : List α} :
    y :: ys ∈ multichoose n.succ (x :: xs) ↔
    y :: ys ∈ multichoose n.succ xs ∨ (y = x ∧ ys ∈ multichoose n (x :: xs)) := by
  simp [multichoose_succ_cons]
  simp [and_comm, eq_comm]

/-- All lists in `multichoose` are composed of elements from the original list. -/
theorem mem_of_mem_multichoose {n : ℕ} {l t : List α} (ht : t ∈ multichoose n l) :
    ∀ u ∈ t, u ∈ l := by
  induction n generalizing t l with
  | zero => simp at ht; simp [ht]
  | succ n ihn =>
    induction l with
    | nil => simp at ht
    | cons y ys ihl =>
      -- Could use `cons_mem_multichoose_succ_cons` here to avoid `∃`; could be messier though.
      rw [mem_multichoose_succ_cons] at ht
      intro u hu
      cases ht with
      | inl ht => simpa using Or.inr (ihl ht u hu)
      | inr ht =>
        rcases ht with ⟨s, hs, ht⟩
        simp [ht] at hu
        cases hu with
        | inl hu => simpa using Or.inl hu
        | inr hu => simpa using ihn hs u hu

/-- All lists in `multichoose` have length `n`. -/
theorem length_of_mem_multichoose {n : ℕ} {l t : List α} (ht : t ∈ multichoose n l) :
    t.length = n := by
  induction n generalizing t l with
  | zero => simp at ht; simp [ht]
  | succ n ihn =>
    induction l with
    | nil => simp at ht
    | cons x xs ihl =>
      simp [mem_multichoose_succ_cons] at ht
      cases ht with
      | inl ht => exact ihl ht
      | inr ht =>
        rcases ht with ⟨s, hs, ht⟩
        simp [ht]
        exact ihn hs

-- TODO: Add more general monotonicity using Sublist `<+`.

-- theorem multichoose_sublist_multichoose {n : ℕ} {l₁ l₂ : List α} (hl : l₁ <+ l₂) :
--     multichoose n l₁ <+ multichoose n l₂ := sorry

lemma mem_multichoose_cons {n : ℕ} {l t : List α} (ht : t ∈ multichoose n l) (x : α) :
    t ∈ multichoose n (x :: l) := by
  cases n with
  | zero => simpa using ht
  | succ n => simp [mem_multichoose_succ_cons, ht]

-- TODO: Generalize and move? Or eliminate?
/-- Two lists are disjoint if some property holds for all elements in one and none in the other. -/
theorem disjoint_of_forall_left {p : α → Prop} {l₁ l₂ : List α}
    (hl₁ : ∀ x ∈ l₁, p x) (hl₂ : ∀ x ∈ l₂, ¬p x) : Disjoint l₁ l₂ :=
  fun x hx₁ hx₂ => hl₂ x hx₂ (hl₁ x hx₁)

/-- Two lists are disjoint if some property holds for all elements in one and none in the other. -/
theorem disjoint_of_forall_right {p : α → Prop} {l₁ l₂ : List α}
    (h₁ : ∀ x ∈ l₁, ¬p x) (h₂ : ∀ x ∈ l₂, p x) : Disjoint l₁ l₂ :=
  (disjoint_of_forall_left h₂ h₁).symm

/-- If the list of elements contains no duplicates, then `multichoose` contains no duplicates. -/
theorem nodup_multichoose {n : ℕ} {l : List α} (hl : Nodup l) : Nodup (multichoose n l) := by
  induction n generalizing l with
  | zero => simp
  | succ n ihn =>
    induction l with
    | nil => simp
    | cons x xs ihl =>
      specialize ihn hl
      simp at hl
      specialize ihl hl.2
      simp [multichoose_succ_cons]
      refine Nodup.append ihl (ihn.map cons_injective) ?_
      refine disjoint_of_forall_right (p := fun l => x ∈ l) ?_ (by simp)
      simp
      intro y hy hx
      refine hl.1 ?_
      exact mem_of_mem_multichoose hy x hx

/-- If a list has no duplicates, then two lists in `multichoose` are a permutation iff equal. -/
theorem perm_mem_multichoose_iff_eq_of_nodup [DecidableEq α] {n : ℕ} {l : List α} (hl : Nodup l)
    {t s : List α} (ht : t ∈ multichoose n l) (hs : s ∈ multichoose n l) :
    t ~ s ↔ t = s := by
  induction n generalizing s t l with
  | zero => simp at ht hs; simp [ht, hs]
  | succ n ihn =>
    induction l with
    | nil => simp at ht
    | cons x xs ihl =>
      specialize @ihn _ hl
      simp at hl
      specialize ihl hl.2
      cases t with
      | nil => simp [eq_comm]
      | cons b bs =>
        cases s with
        | nil => simp [eq_comm]
        | cons c cs =>
          -- Must consider four cases:
          -- (1) `t` and `s` both use `x` (induction on `n`)
          -- (2) `t` and `s` both use only `xs` (induction on `l`)
          -- (3,4) only one of `t` and `s` uses `x` (not equal)
          simp [cons_mem_multichoose_succ_cons] at ht hs
          cases ht with
          | inr ht =>
            cases hs with
            | inr hs =>
              -- (1) `t` and `s` both use `x` (induction on `n`)
              simpa [ht.1, hs.1] using ihn ht.2 hs.2
            | inl hs =>
              -- (3,4) only one of `t` and `s` uses `x` (not equal)
              rw [ht.1]
              replace hs := mem_of_mem_multichoose hs
              simp at hs
              have hc : x ≠ c := fun hx => by rw [← hx] at hs; exact hl.1 hs.1
              have hcs : x ∉ cs := fun hx => hl.1 (hs.2 x hx)
              simp [cons_perm_iff_perm_erase, hc, hcs]
          | inl ht =>
            cases hs with
            | inl hs =>
              -- (2) `t` and `s` both use only `xs` (induction on `l`)
              exact ihl ht hs
            | inr hs =>
              -- (3,4) only one of `t` and `s` uses `x` (not equal)
              rw [hs.1]
              replace ht := mem_of_mem_multichoose ht
              simp at ht
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
      -- simp only [mem_cons] at ht_mem
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

-- TODO(jvlmdr): Should these be in `std`? Or eliminate?

/-- `join` is a sublist of `join` if all pairs are sublists. -/
theorem Sublist.join_of_forall_sublist {s l : List (List α)} (h_len : s.length ≤ l.length)
    (h_sub : ∀ p ∈ List.zip s l, p.1 <+ p.2) : List.join s <+ List.join l := by
  induction s generalizing l with
  | nil => simp
  | cons x s ih =>
    cases l with
    | nil => contradiction
    | cons y l =>
      simp [Nat.succ_le_succ_iff] at h_sub h_len ⊢
      refine List.Sublist.append h_sub.1 ?_
      exact ih h_len (fun p => h_sub.2 p.1 p.2)

/-- `join` is a sublist of `join` if all pairs are sublists. -/
theorem Sublist.join_map_of_forall_sublist {β : Type*} {f g : β → List α} {l : List β}
    (h_sub : ∀ t, f t <+ g t) : List.join (l.map f) <+ List.join (l.map g) := by
  refine join_of_forall_sublist (by simp) ?_
  simp [zip_map']
  intro t _
  exact h_sub t

/-- The `multichoose` list is a sublist of `sublistsLen n` with all elements repeated `n` times. -/
theorem multichoose_sublist_sublistsLen_join_map_replicate {n : ℕ} {l : List α} :
    multichoose n l <+ sublistsLen n (l.map (replicate n)).join := by
  induction n generalizing l with
  | zero => simp
  | succ n ihn =>
    induction l with
    | nil => simp
    | cons x xs ihl =>
      simp [multichoose_succ_cons]
      refine Sublist.append ?_ ?_
      · refine Sublist.trans ihl ?_
        exact sublistsLen_sublist_of_sublist n.succ (by simp)
      · refine Sublist.map (cons x) ?_
        refine Sublist.trans ihn ?_
        refine sublistsLen_sublist_of_sublist n ?_
        simp
        exact Sublist.join_map_of_forall_sublist (by simp)

end List

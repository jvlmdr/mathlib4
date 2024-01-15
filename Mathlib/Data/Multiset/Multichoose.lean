import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.List.Multichoose
import Mathlib.Data.Multiset.Basic

open scoped BigOperators List

variable {α : Type*} [DecidableEq α]

namespace Multiset

-- -- TODO: Move?
-- theorem count_toList {x : α} {t : Multiset α} : t.toList.count x = t.count x := by
--   rw [← coe_count]
--   refine Quotient.inductionOn t ?_
--   simp

section Aux

/-- Helper for `multichoose` that maps a list to a list. -/
def multichooseAux (n : ℕ) (l : List α) : List (Multiset α) := (l.multichoose n).map (↑)

lemma multichooseAux_eq_map_coe {n : ℕ} {l : List α} :
    multichooseAux n l = (l.multichoose n).map (↑) := rfl

@[simp]
lemma multichooseAux_zero {l : List α} : multichooseAux 0 l = [{}] := by simp [multichooseAux]

@[simp]
lemma multichooseAux_succ_nil {n : ℕ} : multichooseAux n.succ ([] : List α) = [] := rfl

lemma multichooseAux_succ_cons {n : ℕ} {x : α} {xs : List α} :
    multichooseAux n.succ (x :: xs) = List.append
      (multichooseAux (n + 1) xs)
      (List.map (cons x) (multichooseAux n (x :: xs))) := by
  simp [multichooseAux, List.multichoose_succ_cons]
  rfl

theorem mem_multichooseAux_iff {n : ℕ} {l : List α} {t : Multiset α} :
    t ∈ multichooseAux n l ↔ card t = n ∧ ∀ x ∈ t, x ∈ l :=
  Quotient.inductionOn t
    (fun t ↦ by simpa [multichooseAux] using List.exists_perm_mem_multichoose_iff)

theorem nodup_multichooseAux {n : ℕ} {l : List α} (hl : List.Nodup l) :
    List.Nodup (multichooseAux n l) := by
  rw [multichooseAux]
  rw [List.nodup_map_iff_inj_on]
  · simp
    intro x hx y hy
    exact (List.perm_mem_multichoose_iff_eq_of_nodup hl hx hy).mp
  · exact List.nodup_multichoose hl

lemma count_cons_multichooseAux_of_not_mem {n : ℕ} {l : List α} {x : α} {t : List α} (hx : x ∉ l) :
    List.count ↑(x :: t) (multichooseAux (n + 1) l) = 0 := by
  induction l with
  | nil => simp
  | cons y l ihl =>
    simp [multichooseAux_succ_cons]
    refine And.intro ?_ ?_
    · exact ihl (List.not_mem_of_not_mem_cons hx)
    · simp [List.count_eq_zero]
      simp [mem_multichooseAux_iff]
      intro s _ hs_mem h
      rw [← cons_coe] at h
      rw [cons_eq_cons] at h
      refine hx ?_
      simp
      cases h with
      | inl h => exact Or.inl h.1.symm
      | inr h =>
        refine hs_mem x ?_
        rcases h with ⟨_, ⟨r, hr⟩⟩
        simp [hr.1]

theorem count_multichooseAux_succ_cons {n : ℕ} {y : α} {l : List α} {t : Multiset α} :
    List.count t (multichooseAux n.succ (y :: l)) =
    List.count t (multichooseAux n.succ l) +
      (if y ∈ t then List.count (t.erase y) (multichooseAux n (y :: l)) else 0) := by
  simp [multichooseAux_succ_cons]
  by_cases h_mem : y ∈ t <;> simp [h_mem]
  · conv => lhs; rw [← cons_erase h_mem]
    exact List.count_map_of_injective _ _ cons_injective_right _
  · simp [List.count_eq_zero]
    intro r _ ht
    simp [← ht] at h_mem

theorem count_multichooseAux_of_card_eq {n : ℕ} {l : List α} {t : Multiset α} (htn : card t = n) :
    (multichooseAux n l).count t = ∏ x in toFinset t, Nat.multichoose (l.count x) (t.count x) := by
  induction n generalizing t l with
  | zero => simp at htn; simp [htn]
  | succ n ihn =>
    induction l with
    | nil =>
      simp
      symm
      rw [Finset.prod_eq_zero_iff]
      simp [Nat.multichoose_zero_eq_zero_iff]
      rw [← card_pos_iff_exists_mem]
      rw [htn]
      exact Nat.succ_pos n
    | cons y l ihl =>
      rw [count_multichooseAux_succ_cons]
      by_cases h_mem : y ∈ t <;> simp [h_mem]
      · -- Split the `y` term from the product.
        -- Use `Nat.multichoose_succ_succ` to split into two terms.
        rw [← Finset.prod_erase_mul _ _ (mem_toFinset.mpr h_mem)]
        rw [List.count_cons_self]
        conv => rhs; rhs; rw [← cons_erase h_mem, count_cons_self]
        rw [Nat.multichoose_succ_succ, mul_add]
        refine congrArg₂ _ ?_ ?_
        · -- Apply induction over `l` for first term.
          rw [ihl]
          simp
          rw [Nat.sub_add_cancel (one_le_count_iff_mem.mpr h_mem)]
          rw [← Finset.prod_erase_mul _ _ (mem_toFinset.mpr h_mem)]
          refine congrArg₂ _ ?_ rfl
          refine Finset.prod_congr rfl ?_
          intro x hx
          rw [Finset.mem_erase] at hx
          rw [List.count_cons_of_ne hx.1]
        · -- Apply induction over `n` for second term.
          rw [ihn (by simp [htn, h_mem])]
          by_cases h_mem' : y ∈ erase t y
          · -- `y ∉ erase t y`; the element for `y` persists in the product
            rw [← Finset.prod_erase_mul (a := y) _ _ (mem_toFinset.mpr h_mem')]
            rw [List.count_cons_self]
            refine congrArg₂ _ ?_ rfl
            refine Finset.prod_congr ?_ ?_
            · ext x
              simp
              intro hx
              exact mem_erase_of_ne hx
            · intro x hx
              refine congrArg₂ _ rfl ?_
              rw [Finset.mem_erase] at hx
              rw [count_erase_of_ne hx.1]
          · -- `y ∉ erase t y`; the element for `y` disappears from the product
            simp [h_mem']
            refine Finset.prod_congr ?_ ?_
            · ext x
              simp
              by_cases hx : x = y <;> simp [hx]
              · exact h_mem'
              · exact mem_erase_of_ne hx
            · intro x hx
              refine congrArg₂ _ rfl ?_
              rw [Finset.mem_erase] at hx
              rw [count_erase_of_ne hx.1]
      · -- `y ∉ t`; count within `y :: l` is same as count within `l`
        rw [ihl]
        refine Finset.prod_congr rfl ?_
        simp
        intro x hx
        rw [List.count_cons_of_ne]
        intro hxy
        rw [hxy] at hx
        exact h_mem hx

theorem count_multichooseAux {n : ℕ} {l : List α} {t : Multiset α} :
    (multichooseAux n l).count t =
    if card t = n then ∏ x in toFinset t, Nat.multichoose (l.count x) (t.count x) else 0 := by
  by_cases h : card t = n <;> simp [h]
  · exact count_multichooseAux_of_card_eq h
  · rw [List.count_eq_zero]
    intro ht
    rw [mem_multichooseAux_iff] at ht
    exact h ht.1  -- contradiction

-- For use with `Quot.liftOn` in `multichoose`.
theorem multichooseAux_perm {n : ℕ} {l₁ l₂ : List α} (hl : l₁ ~ l₂) :
    multichooseAux n l₁ ~ multichooseAux n l₂ := by
  rw [List.perm_iff_count]
  simp [count_multichooseAux, hl.count_eq]

theorem length_multichooseAux {n : ℕ} {l : List α} :
    (multichooseAux n l).length = Nat.multichoose (l.length) n := by
  rw [multichooseAux_eq_map_coe]
  rw [List.length_map]
  exact List.length_multichoose

end Aux


/-- The multisets obtained by choosing `n` elements from a multiset with replacement. -/
def multichoose (n : ℕ) (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s
    (fun l => multichooseAux n l)
    (fun _ _ h => Quot.sound (multichooseAux_perm h))

theorem multichoose_coe' (n : ℕ) (l : List α) :
    multichoose n (↑l : Multiset α) = ↑(multichooseAux n l) := rfl

theorem multichoose_coe (n : ℕ) (l : List α) :
    multichoose n (↑l : Multiset α) = ↑(List.map (↑) (List.multichoose n l) : List (Multiset α)) :=
  rfl

@[simp]
theorem multichoose_zero {s : Multiset α} : multichoose 0 s = {0} :=
  Quotient.inductionOn s fun l => by simp [multichoose_coe']

@[simp]
theorem multichoose_succ_zero {n : ℕ} : multichoose n.succ (0 : Multiset α) = 0 := by
  generalize hs : (0 : Multiset α) = s
  rw [eq_comm] at hs
  revert hs
  refine Quotient.inductionOn s ?_
  simp [multichoose_coe']

theorem multichoose_succ_cons {n : ℕ} {x : α} {s : Multiset α} :
    multichoose n.succ (x ::ₘ s) =
    multichoose n.succ s + (multichoose n (x ::ₘ s)).map (cons x) := by
  refine Quotient.inductionOn s ?_
  intro l
  simp [multichoose_coe']
  simp [multichooseAux_succ_cons]

theorem mem_multichoose_iff {n : ℕ} {s : Multiset α} {t : Multiset α} :
    t ∈ multichoose n s ↔ card t = n ∧ ∀ x ∈ t, x ∈ s :=
  Quotient.inductionOn s fun l => by
    simp [multichoose_coe']
    exact mem_multichooseAux_iff

theorem count_multichoose {n : ℕ} {s : Multiset α} {t : Multiset α} :
    (multichoose n s).count t =
    if card t = n then ∏ x in toFinset t, Nat.multichoose (s.count x) (t.count x) else 0 :=
  Quotient.inductionOn s fun l => by
    simp [multichoose_coe']
    exact count_multichooseAux

theorem count_multichoose_of_card_eq {n : ℕ} {s : Multiset α} {t : Multiset α} (ht : card t = n) :
    (multichoose n s).count t = ∏ x in toFinset t, Nat.multichoose (s.count x) (t.count x) := by
  simp [count_multichoose, ht]

theorem count_multichoose_of_card_ne {n : ℕ} {s : Multiset α} {t : Multiset α} (ht : card t ≠ n) :
    (multichoose n s).count t = 0 := by
  simp [count_multichoose, ht]

theorem nodup_multichoose {n : ℕ} {s : Multiset α} : Nodup s → Nodup (multichoose n s) :=
  Quotient.inductionOn s fun l => by
    simp [multichoose_coe']
    exact nodup_multichooseAux

theorem card_multichoose {n : ℕ} {s : Multiset α} :
    card (multichoose n s) = Nat.multichoose (card s) n :=
  Quotient.inductionOn s fun l => by
    simp [multichoose_coe']
    exact length_multichooseAux

lemma multichoose_singleton {n : ℕ} {x : α} : multichoose n {x} = {replicate n x} := by
  -- Avoid passing through `multichooseAux`.
  induction n with
  | zero => simp
  | succ n ihn =>
    change multichoose (Nat.succ n) (x ::ₘ 0) = {replicate (Nat.succ n) x}
    rw [multichoose_succ_cons]
    simp [ihn]

lemma multichoose_one {s : Multiset α} : multichoose 1 s = s.map (fun x => {x}) :=
  Quotient.inductionOn s fun l => by
    rw [quot_mk_to_coe, coe_map, multichoose_coe', multichooseAux,
      List.multichoose_one, List.map_map, List.map_reverse, coe_reverse]
    rfl

section Powerset  -- For showing that `multichoose` is a subset of `powersetCard n ∘ nsmul n`.

theorem count_powersetAux'_cons {y : α} {l : List α} {t : Multiset α} :
    List.count t (powersetAux' (y :: l)) =
    List.count t (powersetAux' l) +
      if y ∈ t then List.count (t.erase y) (powersetAux' l) else 0 := by
  -- NB: Proof identical to that of `count_powersetAux_succ_cons`.
  simp
  by_cases h_mem : y ∈ t <;> simp [h_mem]
  · conv => lhs; rw [← cons_erase h_mem]
    exact List.count_map_of_injective _ _ cons_injective_right _
  · simp [List.count_eq_zero]
    intro r _ ht
    simp [← ht] at h_mem

theorem count_powersetAux' {l : List α} {t : Multiset α} :
    (powersetAux' l).count t = ∏ x in toFinset t, Nat.choose (l.count x) (t.count x) := by
  induction l generalizing t with
  | nil =>
    simp
    rw [List.count_singleton']
    by_cases ht : t = 0
    · simp [ht]
    · simp [ht]
      symm
      rw [Finset.prod_eq_zero_iff]
      simp [Nat.choose_eq_zero_iff, count_pos]
      rw [← card_pos_iff_exists_mem]
      exact card_pos.mpr ht
  | cons y l ihl =>
    rw [count_powersetAux'_cons]
    by_cases h_mem : y ∈ t <;> simp [h_mem]
    · rw [← Finset.prod_erase_mul _ _ (mem_toFinset.mpr h_mem)]
      rw [List.count_cons_self]
      conv => rhs; rhs; rw [← cons_erase h_mem, count_cons_self]
      rw [Nat.choose_succ_succ, mul_add]
      conv => rhs; rw [add_comm]  -- `powersetAux'` uses the reverse order.
      refine congrArg₂ _ ?_ ?_
      · rw [ihl]
        rw [count_erase_self]
        rw [Nat.sub_one, Nat.succ_pred (count_ne_zero.mpr h_mem)]
        rw [← Finset.prod_erase_mul _ _ (mem_toFinset.mpr h_mem)]
        refine congrArg₂ _ ?_ rfl
        refine Finset.prod_congr rfl ?_
        intro x hx
        rw [Finset.mem_erase] at hx
        simp [hx.1]
      · rw [ihl]
        by_cases h_mem' : y ∈ erase t y
        · rw [← Finset.prod_erase_mul _ _ (mem_toFinset.mpr h_mem')]
          refine congrArg₂ _ ?_ rfl
          refine Finset.prod_congr ?_ ?_
          · ext x
            simp
            intro hx
            exact mem_erase_of_ne hx
          · intro x hx
            rw [Finset.mem_erase] at hx
            simp [hx.1]
        · -- `y ∉ erase t y`; the element for `y` disappears from the product
          simp [h_mem']
          refine Finset.prod_congr ?_ ?_
          · ext x
            simp
            by_cases hx : x = y <;> simp [hx]
            · exact h_mem'
            · exact mem_erase_of_ne hx
          · intro x hx
            rw [Finset.mem_erase] at hx
            simp [hx.1]
    · -- `y ∉ t`; count within `y :: l` is same as count within `l`
      rw [ihl]
      refine Finset.prod_congr rfl ?_
      simp
      intro x hx
      rw [List.count_cons_of_ne]
      intro hxy
      rw [hxy] at hx
      exact h_mem hx

theorem count_powersetAux {l : List α} {t : Multiset α} :
    (powersetAux l).count t = ∏ x in toFinset t, Nat.choose (l.count x) (t.count x) := by
  rw [List.Perm.count_eq powersetAux_perm_powersetAux']
  exact count_powersetAux'

theorem count_powersetAuxCard_cons {n : ℕ} {y : α} {l : List α} {t : Multiset α} :
    List.count t (powersetCardAux n.succ (y :: l)) =
    List.count t (powersetCardAux n.succ l) +
      if y ∈ t then List.count (t.erase y) (powersetCardAux n l) else 0 := by
  simp
  by_cases h_mem : y ∈ t <;> simp [h_mem]
  · conv => lhs; rw [← cons_erase h_mem]
    exact List.count_map_of_injective _ _ cons_injective_right _
  · simp [List.count_eq_zero]
    intro r _ _ ht
    simp [← ht] at h_mem

theorem count_powersetCardAux_of_card_eq {n : ℕ} {l : List α} {t : Multiset α} (htn : card t = n) :
    List.count t (powersetCardAux n l) = ∏ x in toFinset t, Nat.choose (l.count x) (t.count x) := by
  induction n generalizing t l with
  | zero => simp at htn; simp [htn]
  | succ n ihn =>
    induction l generalizing t with
    | nil =>
      simp
      symm
      rw [Finset.prod_eq_zero_iff]
      simp [Nat.choose_eq_zero_iff, count_pos]
      rw [← card_pos_iff_exists_mem]
      simp [htn]
    | cons y l ihl =>
      rw [count_powersetAuxCard_cons]
      by_cases h_mem : y ∈ t <;> simp [h_mem]
      · rw [← Finset.prod_erase_mul _ _ (mem_toFinset.mpr h_mem)]
        rw [List.count_cons_self]
        conv => rhs; rhs; rw [← cons_erase h_mem, count_cons_self]
        rw [Nat.choose_succ_succ, mul_add]
        conv => rhs; rw [add_comm]  -- `powersetCardAux` uses the reverse order.
        refine congrArg₂ _ ?_ ?_
        · rw [ihl htn]
          rw [count_erase_self]
          rw [Nat.sub_one, Nat.succ_pred (count_ne_zero.mpr h_mem)]
          rw [← Finset.prod_erase_mul _ _ (mem_toFinset.mpr h_mem)]
          refine congrArg₂ _ ?_ rfl
          refine Finset.prod_congr rfl ?_
          intro x hx
          rw [Finset.mem_erase] at hx
          simp [hx.1]
        · rw [ihn (by simp [htn, h_mem])]
          by_cases h_mem' : y ∈ erase t y
          · rw [← Finset.prod_erase_mul _ _ (mem_toFinset.mpr h_mem')]
            refine congrArg₂ _ ?_ rfl
            refine Finset.prod_congr ?_ ?_
            · ext x
              simp
              intro hx
              exact mem_erase_of_ne hx
            · intro x hx
              rw [Finset.mem_erase] at hx
              simp [hx.1]
          · -- `y ∉ erase t y`; the element for `y` disappears from the product
            simp [h_mem']
            refine Finset.prod_congr ?_ ?_
            · ext x
              simp
              by_cases hx : x = y <;> simp [hx]
              · exact h_mem'
              · exact mem_erase_of_ne hx
            · intro x hx
              rw [Finset.mem_erase] at hx
              simp [hx.1]
      · -- `y ∉ t`; count within `y :: l` is same as count within `l`
        rw [ihl htn]
        refine Finset.prod_congr rfl ?_
        simp
        intro x hx
        rw [List.count_cons_of_ne]
        intro hxy
        rw [hxy] at hx
        exact h_mem hx


theorem count_powersetCardAux {n : ℕ} {l : List α} {t : Multiset α} :
    (powersetCardAux n l).count t =
    if card t = n then ∏ x in toFinset t, Nat.choose (l.count x) (t.count x) else 0 := by
  by_cases h : card t = n <;> simp [h]
  exact count_powersetCardAux_of_card_eq h

/-- The number of times that each combination appears in `powerset`. -/
theorem count_powerset {s : Multiset α} {t : Multiset α} :
    (powerset s).count t = ∏ x in toFinset t, Nat.choose (s.count x) (t.count x) :=
  Quotient.inductionOn s fun _ => by simpa using count_powersetAux'

/-- The number of times that each combination appears in `powerset`. -/
theorem count_powersetCard {n : ℕ} {s : Multiset α} {t : Multiset α} :
    (powersetCard n s).count t =
    if card t = n then ∏ x in toFinset t, Nat.choose (s.count x) (t.count x) else 0 :=
  Quotient.inductionOn s fun _ => by
    simp [Multiset.powersetCard_coe']
    exact count_powersetCardAux

/-- The number of times that each combination appears in `powerset`. -/
theorem count_powersetCard_of_card_eq {n : ℕ} {s : Multiset α} {t : Multiset α} (ht : card t = n) :
    (powersetCard n s).count t = ∏ x in toFinset t, Nat.choose (s.count x) (t.count x) :=
  Quotient.inductionOn s fun l => by
    simp [Multiset.powersetCard_coe']
    rw [count_powersetCardAux_of_card_eq ht]

end Powerset

lemma multichoose_le_powersetCard_nsmul {n : ℕ} {s : Multiset α} :
    multichoose n s ≤ powersetCard n (n • s) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [le_iff_count]
    intro t
    rw [count_multichoose, count_powersetCard]
    by_cases ht : card t = n.succ <;> simp [ht]
    refine Finset.prod_le_prod (by simp) ?_
    simp
    intro x hxt
    by_cases hxs : x ∈ s
    · rw [Nat.multichoose_eq]
      refine Nat.choose_le_choose _ ?_
      simp [Nat.succ_max_succ]
      rw [Nat.succ_mul]
      rw [add_rotate]
      rw [add_assoc]
      simp
      refine le_trans (count_le_card _ _) ?_
      rw [ht]
      rw [add_comm]
      rw [Nat.succ_le_succ_iff]
      exact Nat.le_mul_of_pos_right n (count_pos.mpr hxs)
    · simp [hxs]
      rw [Nat.choose_eq_zero_of_lt (count_pos.mpr hxt)]
      rw [Nat.multichoose_zero_eq_zero_of_ne]
      exact count_ne_zero.mpr hxt

end Multiset  -- namespace

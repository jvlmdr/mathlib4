/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Eric Wieser, Bhavik Mehta
-/

import Mathlib.Data.Finset.Antidiagonal
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval

/-! # Partial HasAntidiagonal for functions with finite support

Let `μ` be an AddCommMonoid.

In `Mathlib.Data.Finset.Antidiagonal` is defined a TypeClass
`HasAntidiagonal μ` which provides a function `μ → Finset (μ × μ)
which maps `n : μ` to a `Finset` of pairs `(a,b)`
such that `a + b = n`.

These functions apply to `ι →₀ ℕ`, more generally to `ι →₀ μ`
under the additional assumption `OrderedSub μ` that make it
a canonically ordered additive monoid.
In fact, we just need an AddMonoid with a compatible order,
finite Iic, such that if a + b = n, then a, b ≤ n,
and any other bound would be OK.

In this file, we provide an analogous definition for `ι →₀ μ`,
with an explicit finiteness condition on the support,
assuming `HasAntidiagonal μ` and `DecidableEq μ`
This Finset could be viewed inside `ι → μ`, but the `Finsupp` condition
provides a natural `DecidableEq` instance.

Consider types `ι` and `μ`, with `AddCommMonoid μ`, `HasAntidiagonal μ` and `DecidableEq μ`.

* `Finset.HasAntidiagonal.piAntidiagonal s n` is the finite set of all functions
  with finite support contained in `s` and sum `n : μ`
  That condition is expressed by `Finset.HasAntidiagonal.mem_piAntidiagonal`
* `Finset.HasAntidiagonal.mem_piAntidiagonal'` rewrites the `Finsupp.sum`
  condition as a `Finset.sum`
* The construction starts with `Finset.HasAntidiagonal.finAntidiagonal`,
  a variant of `Finset.Nat.antidiagonalTuple`

-/

namespace Finset

open scoped BigOperators

open Function Fin Finsupp HasAntidiagonal

namespace HasAntidiagonal

section Fin

variable {μ : Type*} [AddCommMonoid μ] [DecidableEq μ] [HasAntidiagonal μ]

/-- `finAntidiagonal d n` is the type of `d`-tuples with sum `n`.

TODO: deduplicate with the less general `Finset.Nat.antidiagonalTuple`. -/
def finAntidiagonal (d : ℕ) (n : μ) : Finset (Fin d → μ) :=
  aux d n
where
  /-- Auxiliary construction for `finAntidiagonal` that bundles a proof of lawfulness
  (`mem_finAntidiagonal`), as this is needed to invoke `disjiUnion`. Using `Finset.disjiUnion` makes
  this computationally much more efficient than using `Finset.biUnion`. -/
  aux (d : ℕ) (n : μ) : {s : Finset (Fin d → μ) // ∀ f, f ∈ s ↔ ∑ i, f i = n} :=
    match d with
    | 0 =>
      if h : n = 0 then
        ⟨{0}, by simp [h, Subsingleton.elim finZeroElim ![]]⟩
      else
        ⟨∅, by simp [Ne.symm h]⟩
    | d + 1 =>
      { val := (antidiagonal n).disjiUnion
          (fun ab => (aux d ab.2).1.map {
              toFun := Fin.cons (ab.1)
              inj' := Fin.cons_right_injective _ })
          (fun i _hi j _hj hij => Finset.disjoint_left.2 fun t hti htj => hij <| by
            simp_rw [Finset.mem_map, Embedding.coeFn_mk] at hti htj
            obtain ⟨ai, hai, hij'⟩ := hti
            obtain ⟨aj, haj, rfl⟩ := htj
            rw [Fin.cons_eq_cons] at hij'
            ext
            · exact hij'.1
            · obtain ⟨-, rfl⟩ := hij'
              rw [← (aux d i.2).prop ai |>.mp hai, ← (aux d j.2).prop ai |>.mp haj])
        property := fun f => by
          simp_rw [mem_disjiUnion, mem_antidiagonal, mem_map, Embedding.coeFn_mk, Prod.exists,
            (aux d _).prop, Fin.sum_univ_succ]
          constructor
          · rintro ⟨a, b, rfl, g, rfl, rfl⟩
            simp only [Fin.cons_zero, Fin.cons_succ]
          · intro hf
            exact ⟨_, _, hf, _, rfl, Fin.cons_self_tail f⟩ }

lemma mem_finAntidiagonal (d : ℕ) (n : μ) (f : Fin d → μ) :
    f ∈ finAntidiagonal d n ↔ ∑ i, f i = n :=
  (finAntidiagonal.aux d n).prop f

/-- `finAntidiagonal₀ d n` is the type of d-tuples with sum `n` -/
def finAntidiagonal₀ (d : ℕ) (n : μ) : Finset (Fin d →₀ μ) :=
  (finAntidiagonal d n).map {
      toFun := fun f =>
        -- this is `Finsupp.onFinset`, but computable
        { toFun := f, support := univ.filter (f · ≠ 0), mem_support_toFun := fun x => by simp }
      inj' := fun _ _ h => FunLike.coe_fn_eq.mpr h }

lemma mem_finAntidiagonal₀' (d : ℕ) (n : μ) (f : Fin d →₀ μ) :
    f ∈ finAntidiagonal₀ d n ↔ univ.sum f = n := by
  simp only [finAntidiagonal₀, mem_map, Embedding.coeFn_mk, ← mem_finAntidiagonal]
  constructor
  · rintro ⟨g, h, rfl⟩
    exact h
  · intro h
    use f, h
    exact Finsupp.ext (congrFun rfl)

lemma mem_finAntidiagonal₀ (d : ℕ) (n : μ) (f : Fin d →₀ μ) :
    f ∈ finAntidiagonal₀ d n ↔ sum f (fun _ x => x) = n := by
  rw [mem_finAntidiagonal₀', sum_of_support_subset f (subset_univ _) _ (fun _ _ => rfl)]

end Fin

section piAntidiagonal

variable {ι : Type*} [DecidableEq ι]

variable {μ : Type*} [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ]

/-- The Finset of functions `ι →₀ μ` with support contained in `s` and sum `n`. -/
def piAntidiagonal (s : Finset ι) (n : μ) : Finset (ι →₀ μ) :=
  let x : Finset (s →₀ μ) :=
    (Fintype.truncEquivFinOfCardEq <| Fintype.card_coe s).lift
      (fun e => (finAntidiagonal₀ s.card n).map (equivCongrLeft e.symm).toEmbedding)
      (fun e1 e2 => Finset.ext fun x => by
        simp only [mem_map_equiv, equivCongrLeft_symm, Equiv.symm_symm, equivCongrLeft_apply,
          mem_finAntidiagonal₀, sum_equivMapDomain])
  x.map
    -- This is a computable version of `embDomain (.subtype _)`
    { toFun := fun f =>
      { support := f.support.map (.subtype _),
        toFun := fun i => if h : i ∈ s then f ⟨_, h⟩ else 0
        mem_support_toFun := fun i => by simp }
      inj' := fun f g h => Finsupp.ext fun i => by
          replace h := FunLike.congr_fun h i.val
          dsimp at h
          simp_rw [dif_pos i.prop] at h
          exact h }

/-- A function belongs to `piAntidiagonal s n`
    iff its support is contained in s and the sum of its components is equal to `n` -/
lemma mem_piAntidiagonal {s : Finset ι} {n : μ} {f : ι →₀ μ} :
    f ∈ piAntidiagonal s n ↔ f.support ⊆ s ∧ Finsupp.sum f (fun _ x => x) = n := by
  simp only [piAntidiagonal, mem_map, Embedding.coeFn_mk, mem_finAntidiagonal₀]
  induction' (Fintype.truncEquivFinOfCardEq <| Fintype.card_coe s) using Trunc.ind with e'
  simp_rw [Trunc.lift_mk, mem_map_equiv, equivCongrLeft_symm, Equiv.symm_symm, equivCongrLeft_apply,
    mem_finAntidiagonal₀, sum_equivMapDomain]
  constructor
  · rintro ⟨f, rfl, rfl⟩
    dsimp [sum]
    constructor
    · exact Finset.coe_subset.mpr (Finset.map_subtype_subset f.support)
    · simp
  · rintro ⟨hsupp, rfl⟩
    refine (restrictSupportEquiv (s : Set ι) μ).surjective.exists.mpr ⟨⟨f, hsupp⟩, ?_, ?_⟩
    · simp_rw [sum, restrictSupportEquiv]
      rw [← sum_subtype_of_mem (p := (· ∈ s)) _ hsupp]
      dsimp [subtypeDomain]
      convert rfl
    · ext i
      replace hsupp := mt <| @hsupp i
      rw [not_mem_support_iff] at hsupp
      dsimp [restrictSupportEquiv]
      split_ifs with h
      · simp [subtypeDomain]
      · exact (hsupp h).symm

end piAntidiagonal

section

variable {ι μ : Type*}

variable [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq ι] [DecidableEq μ]

lemma mem_piAntidiagonal' (s : Finset ι) (n : μ) (f) :
    f ∈ piAntidiagonal s n ↔ f.support ≤ s ∧ s.sum f = n := by
  rw [mem_piAntidiagonal]
  simp only [le_eq_subset, and_congr_right_iff]
  intro hs
  rw [sum_of_support_subset _ hs]
  exact fun _ _ => rfl

@[simp]
theorem piAntidiagonal_empty_of_zero :
    piAntidiagonal (∅ : Finset ι) (0 : μ) = {0} := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [le_eq_subset, mem_singleton, subset_empty]
  rw [support_eq_empty, and_iff_left_iff_imp]
  intro hf
  rw [hf, sum_zero_index]

theorem piAntidiagonal_empty_of_ne_zero {n : μ} (hn : n ≠ 0) :
    piAntidiagonal (∅ : Finset ι) n = ∅ := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [le_eq_subset, subset_empty, support_eq_empty, sum_empty,
    not_mem_empty, iff_false, not_and]
  intro hf
  rw [hf, sum_zero_index]
  exact Ne.symm hn

theorem piAntidiagonal_empty [DecidableEq μ] (n : μ) :
    piAntidiagonal (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  split_ifs with hn
  · rw [hn]
    apply piAntidiagonal_empty_of_zero
  · apply piAntidiagonal_empty_of_ne_zero hn

theorem mem_piAntidiagonal_insert [DecidableEq ι] {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) {f : ι →₀ μ} :
    f ∈ piAntidiagonal (insert a s) n ↔
      ∃ m ∈ antidiagonal n, ∃ (g : ι →₀ μ),
        f = Finsupp.update g a m.1 ∧ g ∈ piAntidiagonal s m.2 := by
  simp only [mem_piAntidiagonal', le_eq_subset, mem_antidiagonal, Prod.exists, sum_insert h]
  constructor
  · rintro ⟨hsupp, rfl⟩
    refine ⟨_, _, rfl, Finsupp.erase a f, ?_, ?_, ?_⟩
    · rw [update_erase, update_self]
    · rwa [support_erase, ← subset_insert_iff]
    · apply sum_congr rfl
      intro x hx
      rw [Finsupp.erase_ne (ne_of_mem_of_not_mem hx h)]
  · rintro ⟨n1, n2, rfl, g, rfl, hgsupp, rfl⟩
    constructor
    · exact (support_update_subset _ _).trans (insert_subset_insert a hgsupp)
    · simp only [coe_update]
      apply congr_arg₂
      · rw [update_same]
      · apply sum_congr rfl
        intro x hx
        rw [update_noteq (ne_of_mem_of_not_mem hx h) n1 ⇑g]

theorem piAntidiagonal_insert [DecidableEq ι] [DecidableEq μ] {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) :
    piAntidiagonal (insert a s) n = (antidiagonal n).biUnion
      (fun p : μ × μ =>
        (piAntidiagonal s p.snd).attach.map
        (Set.InjOn.embedding (f := fun f => Finsupp.update f a p.fst)
        (fun f hf g hg => by
          simp only [mem_val, mem_piAntidiagonal] at hf hg
          simp only [FunLike.ext_iff]
          apply forall_imp
          intro x
          by_cases hx : x = a
          · intro _
            have : g x = 0
            · rw [← not_mem_support_iff, hx]
              exact fun hx' => h (hg.1 hx')
            rw [this]
            · rw [← not_mem_support_iff, hx]
              exact fun hx' => h (hf.1 hx')
          · simp only [coe_update, ne_eq, Function.update, dif_neg hx]
            exact id))) := by
  ext f
  rw [mem_piAntidiagonal_insert h, mem_biUnion]
  apply exists_congr
  rintro ⟨n1, n2⟩
  apply and_congr_right'
  simp only [mem_map, mem_attach, true_and, Subtype.exists]
  apply exists_congr
  intro g
  constructor
  · rintro ⟨hf, hg⟩
    use hg
    rw [hf]
    apply symm
    ext x
    simp
  · rintro ⟨hg, hf⟩
    constructor
    · ext x
      rw [← hf]
      simp
    · exact hg

-- This should work under the assumption that e is an embedding and an AddHom
lemma mapRange_piAntidiagonal_subset {μ' : Type*} [AddCommMonoid μ']
    [HasAntidiagonal μ'] [DecidableEq μ']
    {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (piAntidiagonal s n).map (mapRange.addEquiv e).toEmbedding ⊆ piAntidiagonal s (e n) := by
  intro f
  simp only [mem_map, mem_piAntidiagonal]
  rintro ⟨g, ⟨hsupp, hsum⟩, rfl⟩
  simp only [AddEquiv.toEquiv_eq_coe, mapRange.addEquiv_toEquiv, Equiv.coe_toEmbedding,
    mapRange.equiv_apply, EquivLike.coe_coe, le_eq_subset]
  constructor
  · exact subset_trans (support_mapRange) hsupp
  · rw [sum_mapRange_index (fun _ => rfl), ← hsum, _root_.map_finsupp_sum]

lemma mapRange_piAntidiagonal_eq {μ' : Type*} [AddCommMonoid μ']
    [HasAntidiagonal μ'] [DecidableEq μ']
    {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (piAntidiagonal s n).map (mapRange.addEquiv e).toEmbedding = piAntidiagonal s (e n) := by
  ext f
  constructor
  · apply mapRange_piAntidiagonal_subset
  · set h := (mapRange.addEquiv e).toEquiv with hh
    intro hf
    have : n = e.symm (e n) := (AddEquiv.eq_symm_apply e).mpr rfl
    rw [mem_map_equiv, this]
    apply mapRange_piAntidiagonal_subset
    rw [← mem_map_equiv]
    convert hf
    rw [map_map, hh]
    convert map_refl
    apply Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

end

section CanonicallyOrderedAddCommMonoid

variable {ι μ : Type*}
variable [CanonicallyOrderedAddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq ι] [DecidableEq μ]

theorem piAntidiagonal_zero (s : Finset ι) :
    piAntidiagonal s (0 : μ) = {(0 : ι →₀ μ)} := by
  ext f
  simp only [mem_piAntidiagonal', mem_singleton, sum_eq_zero_iff, le_eq_subset]
  constructor
  · rintro ⟨hsupp, hsum⟩
    ext x
    by_cases hx : x ∈ f.support
    · exact hsum x (hsupp hx)
    · simpa only [mem_support_iff, ne_eq, not_not] using hx
  · intro hf
    simp [hf]

end CanonicallyOrderedAddCommMonoid

end HasAntidiagonal

end Finset

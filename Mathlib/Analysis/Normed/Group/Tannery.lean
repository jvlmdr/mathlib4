/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.Data.IsROrC.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Tannery's theorem

Tannery's theorem gives a sufficient criterion for the limit of an infinite sum (with respect to
an auxiliary parameter) to equal the sum of the pointwise limits. See
https://en.wikipedia.org/wiki/Tannery%27s_theorem. It is a special case of the dominated convergence
theorem (with the measure chosen to be the counting measure); but we give here a direct proof, in
order to avoid some unnecessary hypotheses that appear when specialising the general
measure-theoretic result.
-/

open Filter Topology

open scoped BigOperators

/-- **Tannery's theorem**: topological sums commute with termwise limits, when the norms of the
summands are uniformly bounded by a summable function.

(This is the special case of the Lebesgue dominated convergence theorem for the counting measure
on a discrete set. However, we prove it under somewhat weaker assumptions than the general
measure-theoretic result, e.g. `G` is not assumed to be an `ℝ`-vector space or second countable,
and the limit is along an arbitrary filter rather than `atTop ℕ`.) -/
lemma tendsto_tsum_of_dominated {α β G : Type*} {𝓕 : Filter α}
    [DecidableEq β] [NormedAddCommGroup G] [CompleteSpace G]
    {f : α → β → G} {g : β → G} {bound : β → ℝ} (h_sum : Summable bound)
    (hab : ∀ k : β, Tendsto (f · k) 𝓕 (𝓝 (g k)))
    (h_bound : ∀ n k, ‖f n k‖ ≤ bound k) :
    Tendsto (∑' k, f · k) 𝓕 (𝓝 (∑' k, g k)) := by
  -- WLOG β is nonempty
  rcases isEmpty_or_nonempty β
  · simpa only [tsum_empty] using tendsto_const_nhds
  -- WLOG 𝓕 ≠ ⊥
  rcases 𝓕.eq_or_neBot with rfl | _
  · simp only [tendsto_bot]
  -- Auxiliary lemmas
  have h_g_le (k : β) : ‖g k‖ ≤ bound k
  · exact le_of_tendsto (tendsto_norm.comp (hab k)) <| eventually_of_forall <| (h_bound · k)
  have h_sumg : Summable (‖g ·‖) :=
    h_sum.of_norm_bounded _ (fun k ↦ (norm_norm (g k)).symm ▸ h_g_le k)
  have h_suma (n : α) : Summable (‖f n ·‖)
  · apply h_sum.of_norm_bounded
    simpa only [norm_norm] using h_bound n
  -- Now main proof, by an `ε / 3` argument
  rw [Metric.tendsto_nhds]
  intro ε hε
  let ⟨S, hS⟩ := h_sum
  rw [HasSum, Metric.tendsto_nhds] at hS
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hS (ε / 3) (by positivity))
  have h1 : ∑' (k : Set.compl T), bound k.val < ε / 3
  · specialize hT T (le_refl _)
    rw [← Metric.tendsto_nhds, ← HasSum] at hS
    have := hS.tsum_eq
    rw [← sum_add_tsum_compl (s := T) h_sum, ← eq_sub_iff_add_eq'] at this
    erw [this]
    refine lt_of_le_of_lt ?_ hT
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    apply Real.le_norm_self
  have h2 : Tendsto (∑ k in T, f · k) 𝓕 (𝓝 (T.sum g)) := tendsto_finset_sum _ (fun i _ ↦ hab i)
  rw [Metric.tendsto_nhds] at h2
  refine (h2 (ε / 3) (by positivity)).mp (eventually_of_forall (fun n hn ↦ ?_))
  rw [dist_eq_norm, ← tsum_sub (h_suma n).of_norm h_sumg.of_norm,
    ← sum_add_tsum_compl (s := T) ((h_suma n).of_norm.sub h_sumg.of_norm),
    (by ring : ε = ε / 3 + (ε / 3 + ε / 3))]
  refine (norm_add_le _ _).trans_lt (add_lt_add ?_ ?_)
  · simpa only [dist_eq_norm, Finset.sum_sub_distrib] using hn
  · rw [tsum_sub ((h_suma n).subtype _).of_norm (h_sumg.subtype _).of_norm]
    refine (norm_sub_le _ _).trans_lt (add_lt_add ?_ ?_)
    · refine ((norm_tsum_le_tsum_norm ((h_suma n).subtype _)).trans ?_).trans_lt h1
      exact tsum_le_tsum (h_bound n ·) ((h_suma n).subtype _) (h_sum.subtype _)
    · refine ((norm_tsum_le_tsum_norm <| h_sumg.subtype _).trans ?_).trans_lt h1
      exact tsum_le_tsum (h_g_le ·) (h_sumg.subtype _) (h_sum.subtype _)

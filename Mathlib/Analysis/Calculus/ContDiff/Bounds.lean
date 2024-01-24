/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Multinomial

#align_import analysis.calculus.cont_diff from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Bounds on higher derivatives

-/


noncomputable section

open scoped Classical BigOperators NNReal Nat

universe u uD uE uF uG

open Set Fin Filter Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {D : Type uD} [NormedAddCommGroup D]
  [NormedSpace 𝕜 D] {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {s s₁ t u : Set E}

/-!## Quantitative bounds -/

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear. This lemma is an auxiliary version
assuming all spaces live in the same universe, to enable an induction. Use instead
`ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear` that removes this assumption. -/
theorem ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux {Du Eu Fu Gu : Type u}
    [NormedAddCommGroup Du] [NormedSpace 𝕜 Du] [NormedAddCommGroup Eu] [NormedSpace 𝕜 Eu]
    [NormedAddCommGroup Fu] [NormedSpace 𝕜 Fu] [NormedAddCommGroup Gu] [NormedSpace 𝕜 Gu]
    (B : Eu →L[𝕜] Fu →L[𝕜] Gu) {f : Du → Eu} {g : Du → Fu} {n : ℕ} {s : Set Du} {x : Du}
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ‖iteratedFDerivWithin 𝕜 n (fun y => B (f y) (g y)) s x‖ ≤
      ‖B‖ * ∑ i in Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
  /- We argue by induction on `n`. The bound is trivial for `n = 0`. For `n + 1`, we write
    the `(n+1)`-th derivative as the `n`-th derivative of the derivative `B f g' + B f' g`,
    and apply the inductive assumption to each of those two terms. For this induction to make sense,
    the spaces of linear maps that appear in the induction should be in the same universe as the
    original spaces, which explains why we assume in the lemma that all spaces live in the same
    universe. -/
  induction' n with n IH generalizing Eu Fu Gu
  · simp only [Nat.zero_eq, norm_iteratedFDerivWithin_zero, zero_add, Finset.range_one,
      Finset.sum_singleton, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, ← mul_assoc]
    apply B.le_op_norm₂
  · have In : (n : ℕ∞) + 1 ≤ n.succ := by simp only [Nat.cast_succ, le_refl]
    -- Porting note: the next line is a hack allowing Lean to find the operator norm instance.
    let norm := @ContinuousLinearMap.hasOpNorm _ _ Eu ((Du →L[𝕜] Fu) →L[𝕜] Du →L[𝕜] Gu) _ _ _ _ _ _
      (RingHom.id 𝕜)
    have I1 :
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s x‖ ≤
          ‖B‖ * ∑ i : ℕ in Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
            ‖iteratedFDerivWithin 𝕜 (n + 1 - i) g s x‖ := by
      calc
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s x‖ ≤
            ‖B.precompR Du‖ * ∑ i : ℕ in Finset.range (n + 1),
              n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
                ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 g s) s x‖ :=
          IH _ (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
        _ ≤ ‖B‖ * ∑ i : ℕ in Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
              ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 g s) s x‖ :=
          (mul_le_mul_of_nonneg_right (B.norm_precompR_le Du)
            (Finset.sum_nonneg' fun i => by positivity))
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl fun i hi => ?_
          rw [Nat.succ_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)),
            ← norm_iteratedFDerivWithin_fderivWithin hs hx]
    -- Porting note: the next line is a hack allowing Lean to find the operator norm instance.
    let norm := @ContinuousLinearMap.hasOpNorm _ _ (Du →L[𝕜] Eu) (Fu →L[𝕜] Du →L[𝕜] Gu) _ _ _ _ _ _
      (RingHom.id 𝕜)
    have I2 :
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x‖ ≤
        ‖B‖ * ∑ i : ℕ in Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 (i + 1) f s x‖ *
          ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
      calc
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x‖ ≤
            ‖B.precompL Du‖ * ∑ i : ℕ in Finset.range (n + 1),
              n.choose i * ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 f s) s x‖ *
                ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
          IH _ (hf.fderivWithin hs In) (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
        _ ≤ ‖B‖ * ∑ i : ℕ in Finset.range (n + 1),
            n.choose i * ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 f s) s x‖ *
              ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
          (mul_le_mul_of_nonneg_right (B.norm_precompL_le Du)
            (Finset.sum_nonneg' fun i => by positivity))
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl fun i _ => ?_
          rw [← norm_iteratedFDerivWithin_fderivWithin hs hx]
    have J : iteratedFDerivWithin 𝕜 n
        (fun y : Du => fderivWithin 𝕜 (fun y : Du => B (f y) (g y)) s y) s x =
          iteratedFDerivWithin 𝕜 n (fun y => B.precompR Du (f y)
            (fderivWithin 𝕜 g s y) + B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x := by
      apply iteratedFDerivWithin_congr (fun y hy => ?_) hx
      have L : (1 : ℕ∞) ≤ n.succ := by
        simpa only [ENat.coe_one, Nat.one_le_cast] using Nat.succ_pos n
      exact B.fderivWithin_of_bilinear (hf.differentiableOn L y hy) (hg.differentiableOn L y hy)
        (hs y hy)
    rw [← norm_iteratedFDerivWithin_fderivWithin hs hx, J]
    have A : ContDiffOn 𝕜 n (fun y => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s :=
      (B.precompR Du).isBoundedBilinearMap.contDiff.comp_contDiff_on₂
        (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
    have A' : ContDiffOn 𝕜 n (fun y => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s :=
      (B.precompL Du).isBoundedBilinearMap.contDiff.comp_contDiff_on₂ (hf.fderivWithin hs In)
        (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
    rw [iteratedFDerivWithin_add_apply' A A' hs hx]
    apply (norm_add_le _ _).trans ((add_le_add I1 I2).trans (le_of_eq ?_))
    simp_rw [← mul_add, mul_assoc]
    congr 1
    exact (Finset.sum_choose_succ_mul
      (fun i j => ‖iteratedFDerivWithin 𝕜 i f s x‖ * ‖iteratedFDerivWithin 𝕜 j g s x‖) n).symm
#align continuous_linear_map.norm_iterated_fderiv_within_le_of_bilinear_aux ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux

set_option maxHeartbeats 700000 in -- 3.5× the default limit
/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ‖B‖ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
theorem ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear (B : E →L[𝕜] F →L[𝕜] G)
    {f : D → E} {g : D → F} {N : ℕ∞} {s : Set D} {x : D} (hf : ContDiffOn 𝕜 N f s)
    (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (hn : (n : ℕ∞) ≤ N) :
    ‖iteratedFDerivWithin 𝕜 n (fun y => B (f y) (g y)) s x‖ ≤
      ‖B‖ * ∑ i in Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
  /- We reduce the bound to the case where all spaces live in the same universe (in which we
    already have proved the result), by using linear isometries between the spaces and their `ULift`
    to a common universe. These linear isometries preserve the norm of the iterated derivative. -/
  let Du : Type max uD uE uF uG := ULift.{max uE uF uG, uD} D
  let Eu : Type max uD uE uF uG := ULift.{max uD uF uG, uE} E
  let Fu : Type max uD uE uF uG := ULift.{max uD uE uG, uF} F
  let Gu : Type max uD uE uF uG := ULift.{max uD uE uF, uG} G
  have isoD : Du ≃ₗᵢ[𝕜] D := LinearIsometryEquiv.ulift 𝕜 D
  have isoE : Eu ≃ₗᵢ[𝕜] E := LinearIsometryEquiv.ulift 𝕜 E
  have isoF : Fu ≃ₗᵢ[𝕜] F := LinearIsometryEquiv.ulift 𝕜 F
  have isoG : Gu ≃ₗᵢ[𝕜] G := LinearIsometryEquiv.ulift 𝕜 G
  -- lift `f` and `g` to versions `fu` and `gu` on the lifted spaces.
  set fu : Du → Eu := isoE.symm ∘ f ∘ isoD with hfu
  set gu : Du → Fu := isoF.symm ∘ g ∘ isoD with hgu
  -- lift the bilinear map `B` to a bilinear map `Bu` on the lifted spaces.
  set Bu₀ : Eu →L[𝕜] Fu →L[𝕜] G := ((B.comp (isoE : Eu →L[𝕜] E)).flip.comp (isoF : Fu →L[𝕜] F)).flip
    with hBu₀
  let Bu : Eu →L[𝕜] Fu →L[𝕜] Gu;
  exact ContinuousLinearMap.compL 𝕜 Eu (Fu →L[𝕜] G) (Fu →L[𝕜] Gu)
    (ContinuousLinearMap.compL 𝕜 Fu G Gu (isoG.symm : G →L[𝕜] Gu)) Bu₀
  have hBu : Bu = ContinuousLinearMap.compL 𝕜 Eu (Fu →L[𝕜] G) (Fu →L[𝕜] Gu)
      (ContinuousLinearMap.compL 𝕜 Fu G Gu (isoG.symm : G →L[𝕜] Gu)) Bu₀ := rfl
  have Bu_eq : (fun y => Bu (fu y) (gu y)) = isoG.symm ∘ (fun y => B (f y) (g y)) ∘ isoD := by
    ext1 y
    -- Porting note: the two blocks of `rw`s below were
    -- ```
    -- simp only [ContinuousLinearMap.compL_apply, Function.comp_apply,
    --   ContinuousLinearMap.coe_comp', LinearIsometryEquiv.coe_coe'',
    --   ContinuousLinearMap.flip_apply, LinearIsometryEquiv.apply_symm_apply]
    -- ```
    rw [hBu]
    iterate 2 rw [ContinuousLinearMap.compL_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply]
    rw [hBu₀]
    iterate 2 rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply]
    rw [hfu, Function.comp_apply, LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.coe_coe'',
      LinearIsometryEquiv.apply_symm_apply isoE, Function.comp_apply,
      hgu, LinearIsometryEquiv.coe_coe'', Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply isoF]
    simp only [Function.comp_apply]
  -- All norms are preserved by the lifting process.
  have Bu_le : ‖Bu‖ ≤ ‖B‖ := by
    refine' ContinuousLinearMap.op_norm_le_bound _ (norm_nonneg _) fun y => _
    refine' ContinuousLinearMap.op_norm_le_bound _ (by positivity) fun x => _
    simp only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, LinearIsometryEquiv.coe_coe'', ContinuousLinearMap.flip_apply,
      LinearIsometryEquiv.norm_map]
    rw [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply]
    iterate 2 rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply]
    simp only [LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.norm_map]
    calc
      ‖B (isoE y) (isoF x)‖ ≤ ‖B (isoE y)‖ * ‖isoF x‖ := ContinuousLinearMap.le_op_norm _ _
      _ ≤ ‖B‖ * ‖isoE y‖ * ‖isoF x‖ := by gcongr; apply ContinuousLinearMap.le_op_norm
      _ = ‖B‖ * ‖y‖ * ‖x‖ := by simp only [LinearIsometryEquiv.norm_map]
  let su := isoD ⁻¹' s
  have hsu : UniqueDiffOn 𝕜 su := isoD.toContinuousLinearEquiv.uniqueDiffOn_preimage_iff.2 hs
  let xu := isoD.symm x
  have hxu : xu ∈ su := by
    simpa only [Set.mem_preimage, LinearIsometryEquiv.apply_symm_apply] using hx
  have xu_x : isoD xu = x := by simp only [LinearIsometryEquiv.apply_symm_apply]
  have hfu : ContDiffOn 𝕜 n fu su :=
    isoE.symm.contDiff.comp_contDiffOn
      ((hf.of_le hn).comp_continuousLinearMap (isoD : Du →L[𝕜] D))
  have hgu : ContDiffOn 𝕜 n gu su :=
    isoF.symm.contDiff.comp_contDiffOn
      ((hg.of_le hn).comp_continuousLinearMap (isoD : Du →L[𝕜] D))
  have Nfu : ∀ i, ‖iteratedFDerivWithin 𝕜 i fu su xu‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖ := by
    intro i
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ hsu hxu]
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right _ _ hs, xu_x]
    rwa [← xu_x] at hx
  have Ngu : ∀ i, ‖iteratedFDerivWithin 𝕜 i gu su xu‖ = ‖iteratedFDerivWithin 𝕜 i g s x‖ := by
    intro i
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ hsu hxu]
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right _ _ hs, xu_x]
    rwa [← xu_x] at hx
  have NBu :
    ‖iteratedFDerivWithin 𝕜 n (fun y => Bu (fu y) (gu y)) su xu‖ =
      ‖iteratedFDerivWithin 𝕜 n (fun y => B (f y) (g y)) s x‖ := by
    rw [Bu_eq]
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ hsu hxu]
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right _ _ hs, xu_x]
    rwa [← xu_x] at hx
  -- state the bound for the lifted objects, and deduce the original bound from it.
  have : ‖iteratedFDerivWithin 𝕜 n (fun y => Bu (fu y) (gu y)) su xu‖ ≤
      ‖Bu‖ * ∑ i in Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i fu su xu‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) gu su xu‖ :=
    Bu.norm_iteratedFDerivWithin_le_of_bilinear_aux hfu hgu hsu hxu
  simp only [Nfu, Ngu, NBu] at this
  apply this.trans (mul_le_mul_of_nonneg_right Bu_le ?_)
  exact Finset.sum_nonneg' fun i => by positivity
#align continuous_linear_map.norm_iterated_fderiv_within_le_of_bilinear ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ‖B‖ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear (B : E →L[𝕜] F →L[𝕜] G) {f : D → E}
    {g : D → F} {N : ℕ∞} (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) (x : D) {n : ℕ}
    (hn : (n : ℕ∞) ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y => B (f y) (g y)) x‖ ≤ ‖B‖ * ∑ i in Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖ := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact B.norm_iteratedFDerivWithin_le_of_bilinear hf.contDiffOn hg.contDiffOn uniqueDiffOn_univ
    (mem_univ x) hn
#align continuous_linear_map.norm_iterated_fderiv_le_of_bilinear ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` within a set in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear of norm at most `1`:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
theorem ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : ℕ∞} {s : Set D} {x : D}
    (hf : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ}
    (hn : (n : ℕ∞) ≤ N) (hB : ‖B‖ ≤ 1) : ‖iteratedFDerivWithin 𝕜 n (fun y => B (f y) (g y)) s x‖ ≤
      ∑ i in Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
  apply (B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hs hx hn).trans
  apply mul_le_of_le_one_left (Finset.sum_nonneg' fun i => ?_) hB
  positivity
#align continuous_linear_map.norm_iterated_fderiv_within_le_of_bilinear_of_le_one ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one

/-- Bounding the norm of the iterated derivative of `B (f x) (g x)` in terms of the
iterated derivatives of `f` and `g` when `B` is bilinear of norm at most `1`:
`‖D^n (x ↦ B (f x) (g x))‖ ≤ ∑_{k ≤ n} n.choose k ‖D^k f‖ ‖D^{n-k} g‖` -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one (B : E →L[𝕜] F →L[𝕜] G)
    {f : D → E} {g : D → F} {N : ℕ∞} (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) (x : D) {n : ℕ}
    (hn : (n : ℕ∞) ≤ N) (hB : ‖B‖ ≤ 1) : ‖iteratedFDeriv 𝕜 n (fun y => B (f y) (g y)) x‖ ≤
      ∑ i in Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖ := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hf.contDiffOn hg.contDiffOn
    uniqueDiffOn_univ (mem_univ x) hn hB
#align continuous_linear_map.norm_iterated_fderiv_le_of_bilinear_of_le_one ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one

section

variable {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]

theorem norm_iteratedFDerivWithin_smul_le {f : E → 𝕜'} {g : E → F} {N : ℕ∞}
    (hf : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) {x : E} (hx : x ∈ s)
    {n : ℕ} (hn : (n : ℕ∞) ≤ N) : ‖iteratedFDerivWithin 𝕜 n (fun y => f y • g y) s x‖ ≤
      ∑ i in Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
  (ContinuousLinearMap.lsmul 𝕜 𝕜' :
    𝕜' →L[𝕜] F →L[𝕜] F).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
      hf hg hs hx hn ContinuousLinearMap.op_norm_lsmul_le
#align norm_iterated_fderiv_within_smul_le norm_iteratedFDerivWithin_smul_le

theorem norm_iteratedFDeriv_smul_le {f : E → 𝕜'} {g : E → F} {N : ℕ∞} (hf : ContDiff 𝕜 N f)
    (hg : ContDiff 𝕜 N g) (x : E) {n : ℕ} (hn : (n : ℕ∞) ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y => f y • g y) x‖ ≤ ∑ i in Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖ :=
  (ContinuousLinearMap.lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] F →L[𝕜] F).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    hf hg x hn ContinuousLinearMap.op_norm_lsmul_le
#align norm_iterated_fderiv_smul_le norm_iteratedFDeriv_smul_le

end

section

variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
variable {A' : Type*} [NormedCommRing A'] [NormedAlgebra 𝕜 A']

theorem norm_iteratedFDerivWithin_mul_le {f : E → A} {g : E → A} {N : ℕ∞} (hf : ContDiffOn 𝕜 N f s)
    (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s) {x : E} (hx : x ∈ s) {n : ℕ}
    (hn : (n : ℕ∞) ≤ N) : ‖iteratedFDerivWithin 𝕜 n (fun y => f y * g y) s x‖ ≤
      ∑ i in Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
  (ContinuousLinearMap.mul 𝕜 A :
    A →L[𝕜] A →L[𝕜] A).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
      hf hg hs hx hn (ContinuousLinearMap.op_norm_mul_le _ _)
#align norm_iterated_fderiv_within_mul_le norm_iteratedFDerivWithin_mul_le

theorem norm_iteratedFDeriv_mul_le {f : E → A} {g : E → A} {N : ℕ∞} (hf : ContDiff 𝕜 N f)
    (hg : ContDiff 𝕜 N g) (x : E) {n : ℕ} (hn : (n : ℕ∞) ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y => f y * g y) x‖ ≤ ∑ i in Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖ := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact norm_iteratedFDerivWithin_mul_le
    hf.contDiffOn hg.contDiffOn uniqueDiffOn_univ (mem_univ x) hn
#align norm_iterated_fderiv_mul_le norm_iteratedFDeriv_mul_le

-- TODO: Move.
@[simp]
theorem Sym.card_coe {α : Type*} {n : ℕ} (s : Sym α n) : Multiset.card (s : Multiset α) = n :=
  s.prop

theorem norm_iteratedFDeriv_prod_le [NormOneClass A'] {ι : Type*} [DecidableEq ι] {u : Finset ι}
    {f : ι → E → A'} {N : ℕ∞} (hf : ∀ i ∈ u, ContDiff 𝕜 N (f i)) (x : E)
    {n : ℕ} (hn : (n : ℕ∞) ≤ N) :
    ‖iteratedFDeriv 𝕜 n (∏ j in u, f j ·) x‖ ≤
      ∑ p in u.sym n, (p : Multiset ι).multinomial *
        ∏ j in u, ‖iteratedFDeriv 𝕜 ((p : Multiset ι).count j) (f j) x‖ := by
  induction u using Finset.induction generalizing n with
  | empty =>
    cases n with
    | zero => simp [Sym.eq_nil_of_card_zero]
    | succ n => simp [iteratedFDeriv_succ_const]
  | @insert i u hi IH =>
    conv => lhs; simp only [Finset.prod_insert hi]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    specialize @IH hf.2
    refine le_trans
      (norm_iteratedFDeriv_mul_le hf.1 (contDiff_prod hf.2) _ hn) ?_
    rw [← Finset.sum_coe_sort (Finset.sym _ _)]
    rw [Finset.sum_equiv (Finset.symInsertEquiv hi) (t := Finset.univ)
      (g := fun (p : (k : Fin n.succ) × u.sym (n - k)) ↦
        ((Finset.symInsertEquiv hi).symm p : Multiset ι).multinomial * ∏ j in insert i u,
          ‖iteratedFDeriv 𝕜 (((Finset.symInsertEquiv hi).symm p : Multiset ι).count j) (f j) x‖)
      (by simp)
      (by
        simp only [Equiv.symm_apply_apply]
        intro p _
        -- TODO: Why doesn't `simp only` reach inside the product?
        -- have := Equiv.symm_apply_apply (Finset.symInsertEquiv hi) p
        -- simp only [Equiv.symm_apply_apply (Finset.symInsertEquiv hi) p]
        refine congrArg _ ?_
        refine congrArg _ ?_
        funext j
        rw [Equiv.symm_apply_apply])]
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.sum_range]
    refine Finset.sum_le_sum ?_
    simp only [Finset.mem_univ, forall_true_left]
    intro m
    simp only [Finset.symInsertEquiv_symm_apply_coe]
    specialize @IH (n - m) (le_trans (WithTop.coe_le_coe.mpr (n.sub_le m)) hn)
    refine le_trans (mul_le_mul_of_nonneg_left IH (by simp [mul_nonneg])) ?_
    rw [Finset.mul_sum, ← Finset.sum_coe_sort]
    refine Finset.sum_le_sum ?_
    simp only [Finset.mem_univ, forall_true_left, Subtype.forall]
    intro p hp
    refine le_of_eq ?_
    rw [Finset.prod_insert hi]
    have hip : i ∉ p := fun h ↦ hi <| (Finset.mem_sym_iff.mp hp) i h
    have h_count : Multiset.count i (Sym.fill i m p : Multiset ι) = m := by
      simp only [Sym.coe_fill, Sym.coe_replicate]
      simp only [Multiset.count_add, Multiset.count_replicate_self]
      rw [Multiset.count_eq_zero_of_not_mem (by simpa [Sym.mem_coe] using hip)]
      simp
    have h_multinomial : (Sym.fill i m p : Multiset ι).multinomial =
        n.choose m * (p : Multiset ι).multinomial := by
      rw [Multiset.multinomial_filter_ne i]
      simp only [Sym.card_coe, h_count]
      simp only [Sym.coe_fill, Sym.coe_replicate, Multiset.filter_add]
      rw [Multiset.filter_eq_self.mpr]
      · rw [Multiset.filter_eq_nil.mpr]
        · simp
        · exact fun j hj ↦ Decidable.not_not.mpr (Multiset.eq_of_mem_replicate hj).symm
      · exact fun j hj h ↦ hip <| by simpa [h] using hj
    rw [h_count, h_multinomial, Nat.cast_mul]
    ring_nf  -- TODO: Was it just lucky that this worked?
    refine congrArg _ (Finset.prod_congr rfl ?_)
    intro j hj
    have hji : j ≠ i := fun h ↦ hi <| by simpa [h] using hj
    simp only [Sym.coe_fill]
    -- simp only [Multiset.count_add]  -- Example of simp not working.
    rw [Multiset.count_add]
    simp only [Sym.coe_replicate]
    rw [Multiset.count_eq_zero_of_not_mem (s := Multiset.replicate m i)]
    · simp
    · simp [Multiset.mem_replicate, hji]

end

/-- If the derivatives within a set of `g` at `f x` are bounded by `C`, and the `i`-th derivative
within a set of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`-th derivative
of `g ∘ f` is bounded by `n! * C * D^n`.
This lemma proves this estimate assuming additionally that two of the spaces live in the same
universe, to make an induction possible. Use instead `norm_iteratedFDerivWithin_comp_le` that
removes this assumption. -/
theorem norm_iteratedFDerivWithin_comp_le_aux {Fu Gu : Type u} [NormedAddCommGroup Fu]
    [NormedSpace 𝕜 Fu] [NormedAddCommGroup Gu] [NormedSpace 𝕜 Gu] {g : Fu → Gu} {f : E → Fu} {n : ℕ}
    {s : Set E} {t : Set Fu} {x : E} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hst : MapsTo f s t) (hx : x ∈ s) {C : ℝ}
    {D : ℝ} (hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin 𝕜 i f s x‖ ≤ D ^ i) :
    ‖iteratedFDerivWithin 𝕜 n (g ∘ f) s x‖ ≤ n ! * C * D ^ n := by
  /- We argue by induction on `n`, using that `D^(n+1) (g ∘ f) = D^n (g ' ∘ f ⬝ f')`. The successive
    derivatives of `g' ∘ f` are controlled thanks to the inductive assumption, and those of `f'` are
    controlled by assumption.
    As composition of linear maps is a bilinear map, one may use
    `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one` to get from these a bound
    on `D^n (g ' ∘ f ⬝ f')`. -/
  induction' n using Nat.case_strong_induction_on with n IH generalizing Gu
  · simpa [norm_iteratedFDerivWithin_zero, Nat.factorial_zero, algebraMap.coe_one, one_mul,
      pow_zero, mul_one, comp_apply] using hC 0 le_rfl
  have M : (n : ℕ∞) < n.succ := Nat.cast_lt.2 n.lt_succ_self
  have Cnonneg : 0 ≤ C := (norm_nonneg _).trans (hC 0 bot_le)
  have Dnonneg : 0 ≤ D := by
    have : 1 ≤ n + 1 := by simp only [le_add_iff_nonneg_left, zero_le']
    simpa only [pow_one] using (norm_nonneg _).trans (hD 1 le_rfl this)
  -- use the inductive assumption to bound the derivatives of `g' ∘ f`.
  have I : ∀ i ∈ Finset.range (n + 1),
      ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 g t ∘ f) s x‖ ≤ i ! * C * D ^ i
  · intro i hi
    simp only [Finset.mem_range_succ_iff] at hi
    apply IH i hi
    · apply hg.fderivWithin ht
      simp only [Nat.cast_succ]
      exact add_le_add_right (Nat.cast_le.2 hi) _
    · apply hf.of_le (Nat.cast_le.2 (hi.trans n.le_succ))
    · intro j hj
      have : ‖iteratedFDerivWithin 𝕜 j (fderivWithin 𝕜 g t) t (f x)‖ =
          ‖iteratedFDerivWithin 𝕜 (j + 1) g t (f x)‖ :=
        by rw [iteratedFDerivWithin_succ_eq_comp_right ht (hst hx), comp_apply,
          LinearIsometryEquiv.norm_map]
      rw [this]
      exact hC (j + 1) (add_le_add (hj.trans hi) le_rfl)
    · intro j hj h'j
      exact hD j hj (h'j.trans (hi.trans n.le_succ))
  -- reformulate `hD` as a bound for the derivatives of `f'`.
  have J : ∀ i, ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 f s) s x‖ ≤ D ^ (n - i + 1) := by
    intro i
    have : ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 f s) s x‖ =
        ‖iteratedFDerivWithin 𝕜 (n - i + 1) f s x‖
    · rw [iteratedFDerivWithin_succ_eq_comp_right hs hx, comp_apply, LinearIsometryEquiv.norm_map]
    rw [this]
    apply hD
    · simp only [le_add_iff_nonneg_left, zero_le']
    · apply Nat.succ_le_succ tsub_le_self
  -- Now put these together: first, notice that we have to bound `D^n (g' ∘ f ⬝ f')`.
  calc
    ‖iteratedFDerivWithin 𝕜 (n + 1) (g ∘ f) s x‖ =
        ‖iteratedFDerivWithin 𝕜 n (fun y : E => fderivWithin 𝕜 (g ∘ f) s y) s x‖ := by
      rw [iteratedFDerivWithin_succ_eq_comp_right hs hx, comp_apply,
        LinearIsometryEquiv.norm_map]
    _ = ‖iteratedFDerivWithin 𝕜 n (fun y : E => ContinuousLinearMap.compL 𝕜 E Fu Gu
        (fderivWithin 𝕜 g t (f y)) (fderivWithin 𝕜 f s y)) s x‖ := by
      have L : (1 : ℕ∞) ≤ n.succ := by simpa only [ENat.coe_one, Nat.one_le_cast] using n.succ_pos
      congr 1
      refine' iteratedFDerivWithin_congr (fun y hy => _) hx _
      apply fderivWithin.comp _ _ _ hst (hs y hy)
      · exact hg.differentiableOn L _ (hst hy)
      · exact hf.differentiableOn L _ hy
    -- bound it using the fact that the composition of linear maps is a bilinear operation,
    -- for which we have bounds for the`n`-th derivative.
    _ ≤ ∑ i in Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 g t ∘ f) s x‖ *
          ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 f s) s x‖ := by
      have A : ContDiffOn 𝕜 n (fderivWithin 𝕜 g t ∘ f) s := by
        apply ContDiffOn.comp _ (hf.of_le M.le) hst
        apply hg.fderivWithin ht
        simp only [Nat.cast_succ, le_refl]
      have B : ContDiffOn 𝕜 n (fderivWithin 𝕜 f s) s := by
        apply hf.fderivWithin hs
        simp only [Nat.cast_succ, le_refl]
      exact (ContinuousLinearMap.compL 𝕜 E Fu Gu).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
        A B hs hx le_rfl (ContinuousLinearMap.norm_compL_le 𝕜 E Fu Gu)
    -- bound each of the terms using the estimates on previous derivatives (that use the inductive
    -- assumption for `g' ∘ f`).
    _ ≤ ∑ i in Finset.range (n + 1), (n.choose i : ℝ) * (i ! * C * D ^ i) * D ^ (n - i + 1) := by
      gcongr with i hi
      · simp only [mul_assoc (n.choose i : ℝ)]
        exact I i hi
      · exact J i
    -- We are left with trivial algebraic manipulations to see that this is smaller than
    -- the claimed bound.
    _ = ∑ i in Finset.range (n + 1),
      -- porting note: had to insert a few more explicit type ascriptions in this and similar
      -- expressions.
        (n ! : ℝ) * ((i ! : ℝ)⁻¹ * i !) * C * (D ^ i * D ^ (n - i + 1)) * ((n - i)! : ℝ)⁻¹ := by
      congr! 1 with i hi
      simp only [Nat.cast_choose ℝ (Finset.mem_range_succ_iff.1 hi), div_eq_inv_mul, mul_inv]
      ring
    _ = ∑ i in Finset.range (n + 1), (n ! : ℝ) * 1 * C * D ^ (n + 1) * ((n - i)! : ℝ)⁻¹ := by
      congr! with i hi
      · apply inv_mul_cancel
        simpa only [Ne.def, Nat.cast_eq_zero] using i.factorial_ne_zero
      · rw [← pow_add]
        congr 1
        rw [Nat.add_succ, Nat.succ_inj']
        exact Nat.add_sub_of_le (Finset.mem_range_succ_iff.1 hi)
    _ ≤ ∑ i in Finset.range (n + 1), (n ! : ℝ) * 1 * C * D ^ (n + 1) * 1 := by
      gcongr with i
      apply inv_le_one
      simpa only [Nat.one_le_cast] using (n - i).factorial_pos
    _ = (n + 1)! * C * D ^ (n + 1) := by
      simp only [mul_assoc, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.factorial_succ, Nat.cast_mul]
#align norm_iterated_fderiv_within_comp_le_aux norm_iteratedFDerivWithin_comp_le_aux

/-- If the derivatives within a set of `g` at `f x` are bounded by `C`, and the `i`-th derivative
within a set of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`-th derivative
of `g ∘ f` is bounded by `n! * C * D^n`. -/
theorem norm_iteratedFDerivWithin_comp_le {g : F → G} {f : E → F} {n : ℕ} {s : Set E} {t : Set F}
    {x : E} {N : ℕ∞} (hg : ContDiffOn 𝕜 N g t) (hf : ContDiffOn 𝕜 N f s) (hn : (n : ℕ∞) ≤ N)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hst : MapsTo f s t) (hx : x ∈ s) {C : ℝ}
    {D : ℝ} (hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin 𝕜 i f s x‖ ≤ D ^ i) :
    ‖iteratedFDerivWithin 𝕜 n (g ∘ f) s x‖ ≤ n ! * C * D ^ n := by
  /- We reduce the bound to the case where all spaces live in the same universe (in which we
    already have proved the result), by using linear isometries between the spaces and their `ULift`
    to a common universe. These linear isometries preserve the norm of the iterated derivative. -/
  let Fu : Type max uF uG := ULift.{uG, uF} F
  let Gu : Type max uF uG := ULift.{uF, uG} G
  have isoF : Fu ≃ₗᵢ[𝕜] F := LinearIsometryEquiv.ulift 𝕜 F
  have isoG : Gu ≃ₗᵢ[𝕜] G := LinearIsometryEquiv.ulift 𝕜 G
  -- lift `f` and `g` to versions `fu` and `gu` on the lifted spaces.
  let fu : E → Fu := isoF.symm ∘ f
  let gu : Fu → Gu := isoG.symm ∘ g ∘ isoF
  let tu := isoF ⁻¹' t
  have htu : UniqueDiffOn 𝕜 tu := isoF.toContinuousLinearEquiv.uniqueDiffOn_preimage_iff.2 ht
  have hstu : MapsTo fu s tu := fun y hy ↦ by
    simpa only [mem_preimage, comp_apply, LinearIsometryEquiv.apply_symm_apply] using hst hy
  have Ffu : isoF (fu x) = f x := by simp only [comp_apply, LinearIsometryEquiv.apply_symm_apply]
  -- All norms are preserved by the lifting process.
  have hfu : ContDiffOn 𝕜 n fu s := isoF.symm.contDiff.comp_contDiffOn (hf.of_le hn)
  have hgu : ContDiffOn 𝕜 n gu tu :=
    isoG.symm.contDiff.comp_contDiffOn
      ((hg.of_le hn).comp_continuousLinearMap (isoF : Fu →L[𝕜] F))
  have Nfu : ∀ i, ‖iteratedFDerivWithin 𝕜 i fu s x‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖ := fun i ↦ by
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ hs hx]
  simp_rw [← Nfu] at hD
  have Ngu : ∀ i,
      ‖iteratedFDerivWithin 𝕜 i gu tu (fu x)‖ = ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ := fun i ↦ by
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ htu (hstu hx)]
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right _ _ ht, Ffu]
    rw [Ffu]
    exact hst hx
  simp_rw [← Ngu] at hC
  have Nfgu :
      ‖iteratedFDerivWithin 𝕜 n (g ∘ f) s x‖ = ‖iteratedFDerivWithin 𝕜 n (gu ∘ fu) s x‖ := by
    have : gu ∘ fu = isoG.symm ∘ g ∘ f := by
      ext x
      simp only [comp_apply, LinearIsometryEquiv.map_eq_iff, LinearIsometryEquiv.apply_symm_apply]
    rw [this, LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left _ _ hs hx]
  -- deduce the required bound from the one for `gu ∘ fu`.
  rw [Nfgu]
  exact norm_iteratedFDerivWithin_comp_le_aux hgu hfu htu hs hstu hx hC hD
#align norm_iterated_fderiv_within_comp_le norm_iteratedFDerivWithin_comp_le

/-- If the derivatives of `g` at `f x` are bounded by `C`, and the `i`-th derivative
of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`-th derivative
of `g ∘ f` is bounded by `n! * C * D^n`. -/
theorem norm_iteratedFDeriv_comp_le {g : F → G} {f : E → F} {n : ℕ} {N : ℕ∞} (hg : ContDiff 𝕜 N g)
    (hf : ContDiff 𝕜 N f) (hn : (n : ℕ∞) ≤ N) (x : E) {C : ℝ} {D : ℝ}
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv 𝕜 i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv 𝕜 i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv 𝕜 n (g ∘ f) x‖ ≤ n ! * C * D ^ n := by
  simp_rw [← iteratedFDerivWithin_univ] at hC hD ⊢
  exact norm_iteratedFDerivWithin_comp_le hg.contDiffOn hf.contDiffOn hn uniqueDiffOn_univ
    uniqueDiffOn_univ (mapsTo_univ _ _) (mem_univ x) hC hD
#align norm_iterated_fderiv_comp_le norm_iteratedFDeriv_comp_le

section Apply

theorem norm_iteratedFDerivWithin_clm_apply {f : E → F →L[𝕜] G} {g : E → F} {s : Set E} {x : E}
    {N : ℕ∞} {n : ℕ} (hf : ContDiffOn 𝕜 N f s) (hg : ContDiffOn 𝕜 N g s) (hs : UniqueDiffOn 𝕜 s)
    (hx : x ∈ s) (hn : ↑n ≤ N) : ‖iteratedFDerivWithin 𝕜 n (fun y => (f y) (g y)) s x‖ ≤
      ∑ i in Finset.range (n + 1), ↑(n.choose i) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
  let B : (F →L[𝕜] G) →L[𝕜] F →L[𝕜] G := ContinuousLinearMap.flip (ContinuousLinearMap.apply 𝕜 G)
  have hB : ‖B‖ ≤ 1 := by
    simp only [ContinuousLinearMap.op_norm_flip, ContinuousLinearMap.apply]
    refine' ContinuousLinearMap.op_norm_le_bound _ zero_le_one fun f => _
    simp only [ContinuousLinearMap.coe_id', id.def, one_mul]
    rfl
  exact B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hf hg hs hx hn hB
#align norm_iterated_fderiv_within_clm_apply norm_iteratedFDerivWithin_clm_apply

theorem norm_iteratedFDeriv_clm_apply {f : E → F →L[𝕜] G} {g : E → F} {N : ℕ∞} {n : ℕ}
    (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) (x : E) (hn : ↑n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y : E => (f y) (g y)) x‖ ≤ ∑ i in Finset.range (n + 1),
      ↑(n.choose i) * ‖iteratedFDeriv 𝕜 i f x‖ * ‖iteratedFDeriv 𝕜 (n - i) g x‖ := by
  simp only [← iteratedFDerivWithin_univ]
  exact norm_iteratedFDerivWithin_clm_apply hf.contDiffOn hg.contDiffOn uniqueDiffOn_univ
    (Set.mem_univ x) hn
#align norm_iterated_fderiv_clm_apply norm_iteratedFDeriv_clm_apply

theorem norm_iteratedFDerivWithin_clm_apply_const {f : E → F →L[𝕜] G} {c : F} {s : Set E} {x : E}
    {N : ℕ∞} {n : ℕ} (hf : ContDiffOn 𝕜 N f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hn : ↑n ≤ N) :
    ‖iteratedFDerivWithin 𝕜 n (fun y : E => (f y) c) s x‖ ≤
      ‖c‖ * ‖iteratedFDerivWithin 𝕜 n f s x‖ := by
  let g : (F →L[𝕜] G) →L[𝕜] G := ContinuousLinearMap.apply 𝕜 G c
  have h := g.norm_compContinuousMultilinearMap_le (iteratedFDerivWithin 𝕜 n f s x)
  rw [← g.iteratedFDerivWithin_comp_left hf hs hx hn] at h
  refine' h.trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _))
  refine' g.op_norm_le_bound (norm_nonneg _) fun f => _
  rw [ContinuousLinearMap.apply_apply, mul_comm]
  exact f.le_op_norm c
#align norm_iterated_fderiv_within_clm_apply_const norm_iteratedFDerivWithin_clm_apply_const

theorem norm_iteratedFDeriv_clm_apply_const {f : E → F →L[𝕜] G} {c : F} {x : E} {N : ℕ∞} {n : ℕ}
    (hf : ContDiff 𝕜 N f) (hn : ↑n ≤ N) :
    ‖iteratedFDeriv 𝕜 n (fun y : E => (f y) c) x‖ ≤ ‖c‖ * ‖iteratedFDeriv 𝕜 n f x‖ := by
  simp only [← iteratedFDerivWithin_univ]
  exact norm_iteratedFDerivWithin_clm_apply_const hf.contDiffOn uniqueDiffOn_univ
    (Set.mem_univ x) hn
#align norm_iterated_fderiv_clm_apply_const norm_iteratedFDeriv_clm_apply_const

end Apply

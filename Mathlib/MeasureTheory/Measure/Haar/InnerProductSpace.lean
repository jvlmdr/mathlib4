/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

#align_import measure_theory.measure.haar.inner_product_space from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Volume forms and measures on inner product spaces

A volume form induces a Lebesgue measure on general finite-dimensional real vector spaces. In this
file, we discuss the specific situation of inner product spaces, where an orientation gives
rise to a canonical volume form. We show that the measure coming from this volume form gives
measure `1` to the parallelepiped spanned by any orthonormal basis, and that it coincides with
the canonical `volume` from the `MeasureSpace` instance.
-/


open FiniteDimensional MeasureTheory MeasureTheory.Measure Set

variable {ι F : Type*}

variable [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

section

variable {m n : ℕ} [_i : Fact (finrank ℝ F = n)]

/-- The volume form coming from an orientation in an inner product space gives measure `1` to the
parallelepiped associated to any orthonormal basis. This is a rephrasing of
`abs_volumeForm_apply_of_orthonormal` in terms of measures. -/
theorem Orientation.measure_orthonormalBasis (o : Orientation ℝ F (Fin n))
    (b : OrthonormalBasis ι ℝ F) : o.volumeForm.measure (parallelepiped b) = 1 := by
  have e : ι ≃ Fin n := by
    refine' Fintype.equivFinOfCardEq _
    rw [← _i.out, finrank_eq_card_basis b.toBasis]
  have A : ⇑b = b.reindex e ∘ e := by
    ext x
    simp only [OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]
  rw [A, parallelepiped_comp_equiv, AlternatingMap.measure_parallelepiped,
    o.abs_volumeForm_apply_of_orthonormal, ENNReal.ofReal_one]
#align orientation.measure_orthonormal_basis Orientation.measure_orthonormalBasis

/-- In an oriented inner product space, the measure coming from the canonical volume form
associated to an orientation coincides with the volume. -/
theorem Orientation.measure_eq_volume (o : Orientation ℝ F (Fin n)) :
    o.volumeForm.measure = volume := by
  have A : o.volumeForm.measure (stdOrthonormalBasis ℝ F).toBasis.parallelepiped = 1 :=
    Orientation.measure_orthonormalBasis o (stdOrthonormalBasis ℝ F)
  rw [addHaarMeasure_unique o.volumeForm.measure
    (stdOrthonormalBasis ℝ F).toBasis.parallelepiped, A, one_smul]
  simp only [volume, Basis.addHaar]
#align orientation.measure_eq_volume Orientation.measure_eq_volume

end

/-- The volume measure in a finite-dimensional inner product space gives measure `1` to the
parallelepiped spanned by any orthonormal basis. -/
theorem OrthonormalBasis.volume_parallelepiped (b : OrthonormalBasis ι ℝ F) :
    volume (parallelepiped b) = 1 := by
  haveI : Fact (finrank ℝ F = finrank ℝ F) := ⟨rfl⟩
  let o := (stdOrthonormalBasis ℝ F).toBasis.orientation
  rw [← o.measure_eq_volume]
  exact o.measure_orthonormalBasis b
#align orthonormal_basis.volume_parallelepiped OrthonormalBasis.volume_parallelepiped

/-- The Haar measure defined by any orthonormal basis of a finite-dimensional inner product space
is equal to its volume measure. -/
theorem OrthonormalBasis.addHaar_eq_volume {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (b : OrthonormalBasis ι ℝ F) :
    b.toBasis.addHaar = volume := by
  rw [Basis.addHaar_eq_iff]
  exact b.volume_parallelepiped

namespace EuclideanSpace

open BigOperators ENNReal

/-- The measure equivalence between `EuclideanSpace ℝ ι` and `ι → ℝ` is volume preserving. -/
theorem volume_preserving_measurableEquiv (ι : Type*) [Fintype ι] :
    MeasurePreserving (EuclideanSpace.measurableEquiv ι) := by
  classical
  convert ((EuclideanSpace.measurableEquiv ι).symm.measurable.measurePreserving _).symm
  rw [eq_comm, ← addHaarMeasure_eq_volume_pi, ← Basis.parallelepiped_basisFun, ← Basis.addHaar_def]
  rw [coe_measurableEquiv_symm, ← PiLp.continuousLinearEquiv_symm_apply 2 ℝ, Basis.map_addHaar]
  rw [Basis.addHaar_eq_iff, ContinuousLinearEquiv.symm_toLinearEquiv]
  exact OrthonormalBasis.volume_parallelepiped (EuclideanSpace.basisFun _ _)

-- See: https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

theorem unit_ball_equiv (ι : Type*) [Fintype ι] :
    (equiv ι ℝ) '' Metric.ball (0 : EuclideanSpace ℝ ι) 1 = {x : ι → ℝ | ∑ i, x i ^ 2 < 1} := by
  ext; simp_rw [PiLp.continuousLinearEquiv_apply, mem_image_equiv, mem_ball_zero_iff, norm_eq,
    WithLp.equiv_symm_pi_apply, Real.norm_eq_abs, sq_abs, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1),
    one_pow, mem_setOf_eq]

@[simp]
theorem volume_ball (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    volume (Metric.ball x r) = NNReal.pi * (ENNReal.ofReal r) ^ 2:= by
  obtain hr | hr := lt_or_le r 0
  · rw [Metric.ball_eq_empty.mpr (le_of_lt hr), measure_empty, ← zero_eq_ofReal.mpr
      (le_of_lt hr), zero_pow zero_lt_two, mul_zero]
  · suffices volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = NNReal.pi by
      rw [Measure.addHaar_ball _ _ hr, finrank_euclideanSpace_fin, ofReal_pow hr, this, mul_comm]
    calc volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
      _ = volume ({x : (Fin 2) → ℝ | ∑ i, x i ^ 2 < 1}) := by
        rw [← unit_ball_equiv, ← coe_continuousLinearEquiv, MeasurableEquiv.image_eq_preimage,
          ← ((volume_preserving_measurableEquiv (Fin 2)).symm).measure_preimage measurableSet_ball]
      _ = volume ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}) := by
        rw [← ((volume_preserving_finTwoArrow ℝ).symm).measure_preimage
          (by rw [← unit_ball_equiv, ← coe_continuousLinearEquiv]
              exact (MeasurableEquiv.measurableSet_image _).mpr measurableSet_ball)]
        simp only [MeasurableEquiv.finTwoArrow_symm_apply, Fin.sum_univ_two, preimage_setOf_eq,
          Fin.cons_zero, Fin.cons_one]
      _ = volume ({p : ℝ × ℝ | (- 1 < p.1 ∧ p.1 ≤ 1) ∧ p.1 ^ 2 + p.2 ^ 2 < 1}) := by
        congr
        refine Set.ext (fun _ => iff_and_self.mpr (fun h => And.imp_right (fun h => le_of_lt h) ?_))
        rw [← abs_lt, ← sq_lt_one_iff_abs_lt_one]
        exact lt_of_add_lt_of_nonneg_left h (sq_nonneg _)
      _ = volume (regionBetween (fun x => - Real.sqrt (1 - x ^ 2)) (fun x => Real.sqrt (1 - x ^ 2))
          (Set.Ioc (-1) 1)) := by
        simp_rw [regionBetween, Set.mem_Ioo, Set.mem_Ioc, ← Real.sq_lt, lt_tsub_iff_left,
          Nat.cast_one]
      _ = ENNReal.ofReal ((2 : ℝ) * ∫ (a : ℝ) in Set.Ioc (-1) 1, Real.sqrt (1 - a ^ 2)) := by
        rw [volume_eq_prod, volume_regionBetween_eq_integral (Continuous.integrableOn_Ioc
          (by continuity)) (Continuous.integrableOn_Ioc (by continuity)) measurableSet_Ioc
          (fun _ _ => neg_le_self (Real.sqrt_nonneg _))]
        simp_rw [Pi.sub_apply, sub_neg_eq_add, ← two_mul, integral_mul_left]
      _ = NNReal.pi := by
        rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), Nat.cast_one,
          integral_sqrt_one_sub_sq, two_mul, add_halves, ← NNReal.coe_real_pi,
          ofReal_coe_nnreal]

end EuclideanSpace

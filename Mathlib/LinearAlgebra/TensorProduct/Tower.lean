/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.Algebra.Algebra.Tower

#align_import ring_theory.tensor_product from "leanprover-community/mathlib"@"88fcdc3da43943f5b01925deddaa5bf0c0e85e4e"

/-!
# The `A`-module structure on `M ⊗[R] N`

When `M` is both an `R`-module and an `A`-module, and `Algebra R A`, then many of the morphisms
preserve the actions by `A`.

This file provides more general versions of the definitions already in
`LinearAlgebra/TensorProduct`.

## Main definitions

 * `TensorProduct.AlgebraTensorModule.curry`
 * `TensorProduct.AlgebraTensorModule.uncurry`
 * `TensorProduct.AlgebraTensorModule.lcurry`
 * `TensorProduct.AlgebraTensorModule.lift`
 * `TensorProduct.AlgebraTensorModule.lift.equiv`
 * `TensorProduct.AlgebraTensorModule.mk`
 * `TensorProduct.AlgebraTensorModule.assoc`

## Implementation notes

We could thus consider replacing the less general definitions with these ones. If we do this, we
probably should still implement the less general ones as abbreviations to the more general ones with
fewer type arguments.
-/

namespace TensorProduct

namespace AlgebraTensorModule

variable {R A M N P : Type _}

open LinearMap
open Algebra (lsmul)

section Semiring

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P] [Module A P] [IsScalarTower R A P]

theorem smul_eq_lsmul_rTensor (a : A) (x : M ⊗[R] N) : a • x = (lsmul R M a).rTensor N x :=
  rfl
#align tensor_product.algebra_tensor_module.smul_eq_lsmul_rtensor TensorProduct.AlgebraTensorModule.smul_eq_lsmul_rTensor

/-- Heterobasic version of `TensorProduct.curry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
nonrec def curry (f : M ⊗[R] N →ₗ[A] P) : M →ₗ[A] N →ₗ[R] P :=
  { curry (f.restrictScalars R) with
    toFun := curry (f.restrictScalars R)
    map_smul' := fun c x => LinearMap.ext fun y => f.map_smul c (x ⊗ₜ y) }
#align tensor_product.algebra_tensor_module.curry TensorProduct.AlgebraTensorModule.curry
#align tensor_product.algebra_tensor_module.curry_apply TensorProduct.AlgebraTensorModule.curry_apply

theorem restrictScalars_curry (f : M ⊗[R] N →ₗ[A] P) :
    restrictScalars R (curry f) = TensorProduct.curry (f.restrictScalars R) :=
  rfl
#align tensor_product.algebra_tensor_module.restrict_scalars_curry TensorProduct.AlgebraTensorModule.restrictScalars_curry

/-- Just as `TensorProduct.ext` is marked `ext` instead of `TensorProduct.ext'`, this is
a better `ext` lemma than `TensorProduct.AlgebraTensorModule.ext` below.

See note [partially-applied ext lemmas]. -/
@[ext high]
nonrec theorem curry_injective : Function.Injective (curry : (M ⊗ N →ₗ[A] P) → M →ₗ[A] N →ₗ[R] P) :=
  fun _ _ h =>
  LinearMap.restrictScalars_injective R <|
    curry_injective <| (congr_arg (LinearMap.restrictScalars R) h : _)
#align tensor_product.algebra_tensor_module.curry_injective TensorProduct.AlgebraTensorModule.curry_injective

theorem ext {g h : M ⊗[R] N →ₗ[A] P} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  curry_injective <| LinearMap.ext₂ H
#align tensor_product.algebra_tensor_module.ext TensorProduct.AlgebraTensorModule.ext

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Algebra R A]

variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P] [Module A P] [IsScalarTower R A P]

/-- Heterobasic version of `TensorProduct.lift`:

Constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P` with the
property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
nonrec def lift (f : M →ₗ[A] N →ₗ[R] P) : M ⊗[R] N →ₗ[A] P :=
  { lift (f.restrictScalars R) with
    map_smul' := fun c =>
      show
        ∀ x : M ⊗[R] N,
          (lift (f.restrictScalars R)).comp (lsmul R _ c) x =
            (lsmul R _ c).comp (lift (f.restrictScalars R)) x
        from
        ext_iff.1 <|
          TensorProduct.ext' fun x y => by
            simp only [comp_apply, Algebra.lsmul_coe, smul_tmul', lift.tmul,
              coe_restrictScalars, f.map_smul, smul_apply] }
#align tensor_product.algebra_tensor_module.lift TensorProduct.AlgebraTensorModule.lift

-- Porting note: autogenerated lemma unfolded to `liftAux`
@[simp]
theorem lift_apply (f : M →ₗ[A] N →ₗ[R] P) (a : M ⊗[R] N) :
    AlgebraTensorModule.lift f a = TensorProduct.lift (LinearMap.restrictScalars R f) a :=
  rfl

@[simp]
theorem lift_tmul (f : M →ₗ[A] N →ₗ[R] P) (x : M) (y : N) : lift f (x ⊗ₜ y) = f x y :=
  rfl
#align tensor_product.algebra_tensor_module.lift_tmul TensorProduct.AlgebraTensorModule.lift_tmul

variable (R A M N P)

/-- Heterobasic version of `TensorProduct.uncurry`:

Linearly constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P`
with the property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps]
def uncurry : (M →ₗ[A] N →ₗ[R] P) →ₗ[A] M ⊗[R] N →ₗ[A] P where
  toFun := lift
  map_add' _ _ := ext fun x y => by simp only [lift_tmul, add_apply]
  map_smul' _ _ := ext fun x y => by simp only [lift_tmul, smul_apply, RingHom.id_apply]
#align tensor_product.algebra_tensor_module.uncurry TensorProduct.AlgebraTensorModule.uncurry

/-- Heterobasic version of `TensorProduct.lcurry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
def lcurry : (M ⊗[R] N →ₗ[A] P) →ₗ[A] M →ₗ[A] N →ₗ[R] P where
  toFun := curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align tensor_product.algebra_tensor_module.lcurry TensorProduct.AlgebraTensorModule.lcurry

/-- Heterobasic version of `TensorProduct.lift.equiv`:

A linear equivalence constructing a linear map `M ⊗[R] N →[A] P` given a
bilinear map `M →[A] N →[R] P` with the property that its composition with the
canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is the given bilinear map `M →[A] N →[R] P`. -/
def lift.equiv : (M →ₗ[A] N →ₗ[R] P) ≃ₗ[A] M ⊗[R] N →ₗ[A] P :=
  LinearEquiv.ofLinear (uncurry R A M N P) (lcurry R A M N P)
    (LinearMap.ext fun _ => ext fun x y => lift_tmul _ x y)
    (LinearMap.ext fun f => LinearMap.ext fun x => LinearMap.ext fun y => lift_tmul f x y)
#align tensor_product.algebra_tensor_module.lift.equiv TensorProduct.AlgebraTensorModule.lift.equiv

/-- Heterobasic version of `TensorProduct.mk`:

The canonical bilinear map `M →[A] N →[R] M ⊗[R] N`. -/
@[simps! apply]
nonrec def mk : M →ₗ[A] N →ₗ[R] M ⊗[R] N :=
  { mk R M N with map_smul' := fun _ _ => rfl }
#align tensor_product.algebra_tensor_module.mk TensorProduct.AlgebraTensorModule.mk
#align tensor_product.algebra_tensor_module.mk_apply TensorProduct.AlgebraTensorModule.mk_apply

attribute [local ext high] TensorProduct.ext

/-- Heterobasic version of `TensorProduct.assoc`:

Linear equivalence between `(M ⊗[A] N) ⊗[R] P` and `M ⊗[A] (N ⊗[R] P)`. -/
def assoc : (M ⊗[A] P) ⊗[R] N ≃ₗ[A] M ⊗[A] P ⊗[R] N :=
  LinearEquiv.ofLinear
    (lift <|
      TensorProduct.uncurry A _ _ _ <| comp (lcurry R A _ _ _) <| TensorProduct.mk A M (P ⊗[R] N))
    (TensorProduct.uncurry A _ _ _ <|
      comp (uncurry R A _ _ _) <| by
        apply TensorProduct.curry
        exact mk R A _ _)
    (by
      ext
      rfl)
    (by
      ext
      -- porting note: was `simp only [...]`
      rfl)
#align tensor_product.algebra_tensor_module.assoc TensorProduct.AlgebraTensorModule.assoc

end CommSemiring

end AlgebraTensorModule

end TensorProduct

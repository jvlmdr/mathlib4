/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Order.GaloisConnection

/-!
# Flooring division

-/

variable {ι α β : Type*}

section OrderedAddCommMonoid
variable (α β) [OrderedAddCommMonoid α] [OrderedAddCommMonoid β] [SMulZeroClass α β]

class FloorDiv where
  /-- Flooring division. If `a > 0`, then `b ⌊/⌋ a` is the greatest `c` such that `a • c ≤ b`. -/
  floorDiv : β → α → β
  /-- Do not use this. Use `gc_floorDiv_smul` or `gc_floorDiv_mul` instead. -/
  protected floorDiv_gc ⦃a⦄ : 0 < a → GaloisConnection (a • ·) (floorDiv · a)
  /-- Do not use this. Use `floorDiv_nonpos` instead. -/
  protected floorDiv_nonpos ⦃a⦄ : a ≤ 0 → ∀ b, floorDiv b a = 0
  /-- Do not use this. Use `zero_floorDiv` instead. -/
  protected zero_floorDiv (a) : floorDiv 0 a = 0

class CeilDiv where
  /-- Ceiling division. If `a > 0`, then `b ⌈/⌉ a` is the least `c` such that `b ≤ a • c`. -/
  ceilDiv : β → α → β
  /-- Do not use this. Use `gc_smul_ceilDiv` or `gc_mul_ceilDiv` instead. -/
  protected ceilDiv_gc ⦃a⦄ : 0 < a → GaloisConnection (ceilDiv · a) (a • ·)
  /-- Do not use this. Use `ceilDiv_nonpos` instead. -/
  protected ceilDiv_nonpos ⦃a⦄ : a ≤ 0 → ∀ b, ceilDiv b a = 0
  /-- Do not use this. Use `zero_ceilDiv` instead. -/
  protected zero_ceilDiv (a) : ceilDiv 0 a = 0

@[inherit_doc] infixl:70 " ⌊/⌋ "   => FloorDiv.floorDiv
@[inherit_doc] infixl:70 " ⌈/⌉ "   => CeilDiv.ceilDiv

variable {α β}

section FloorDiv
variable [FloorDiv α β] {a : α} {b c : β}

lemma gc_floorDiv_smul (ha : 0 < a) : GaloisConnection (a • · : β → β) (· ⌊/⌋ a) :=
  FloorDiv.floorDiv_gc ha

@[simp] lemma le_floorDiv_iff_smul_le (ha : 0 < a) : c ≤ b ⌊/⌋ a ↔ a • c ≤ b :=
  (gc_floorDiv_smul ha _ _).symm

@[simp] lemma floorDiv_of_nonpos (ha : a ≤ 0) (b : β) : b ⌊/⌋ a = 0 := FloorDiv.floorDiv_nonpos ha _
lemma floorDiv_zero (b : β) : b ⌊/⌋ (0 : α) = 0 := by simp
@[simp] lemma zero_floorDiv (a : α) : (0 : β) ⌊/⌋ a = 0 := FloorDiv.zero_floorDiv _

end FloorDiv

section CeilDiv
variable [CeilDiv α β] {a : α} {b c : β}

lemma gc_smul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a • · : β → β) :=
  CeilDiv.ceilDiv_gc ha

@[simp]
lemma ceilDiv_le_iff_le_smul (ha : 0 < a) : b ⌈/⌉ a ≤ c ↔ b ≤ a • c := gc_smul_ceilDiv ha _ _

@[simp] lemma ceilDiv_of_nonpos (ha : a ≤ 0) (b : β) : b ⌈/⌉ a = 0 := CeilDiv.ceilDiv_nonpos ha _
lemma ceilDiv_zero (b : β) : b ⌈/⌉ (0 : α) = 0 := by simp
@[simp] lemma zero_ceilDiv (a : α) : (0 : β) ⌈/⌉ a = 0 := CeilDiv.zero_ceilDiv _

end CeilDiv
end OrderedAddCommMonoid

section OrderedSemiring
variable [OrderedSemiring α] [OrderedAddCommMonoid β] [MulActionWithZero α β]

section FloorDiv
variable [FloorDiv α β] {a : α}

@[simp] lemma floorDiv_one [Nontrivial α] (b : β) : b ⌊/⌋ (1 : α) = b :=
  eq_of_forall_le_iff $ fun c ↦ by simp [zero_lt_one' α]

@[simp] lemma smul_floorDiv [PosSMulMono α β] [PosSMulMonoRev α β] (ha : 0 < a) (b : β) :
    a • b ⌊/⌋ a = b :=
  eq_of_forall_le_iff $ by simp [smul_le_smul_iff_of_pos_left, ha]

end FloorDiv

section CeilDiv
variable [CeilDiv α β] {a : α}

@[simp] lemma ceilDiv_one [Nontrivial α] (b : β) : b ⌈/⌉ (1 : α) = b :=
  eq_of_forall_ge_iff $ fun c ↦ by simp [zero_lt_one' α]

@[simp] lemma smul_ceilDiv [PosSMulMono α β] [PosSMulMonoRev α β] (ha : 0 < a) (b : β) :
    a • b ⌈/⌉ a = b :=
  eq_of_forall_ge_iff $ by simp [smul_le_smul_iff_of_pos_left, ha]

end CeilDiv

section FloorDiv
variable [FloorDiv α α] {a b c : α}

lemma gc_floorDiv_mul (ha : 0 < a) : GaloisConnection (a * ·) (· ⌊/⌋ a) := gc_floorDiv_smul ha
lemma le_floorDiv_iff_mul_le (ha : 0 < a) : c ≤ b ⌊/⌋ a ↔ a • c ≤ b := le_floorDiv_iff_smul_le ha

end FloorDiv

section CeilDiv
variable [CeilDiv α α] {a b c : α}

lemma gc_mul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a * ·) := gc_smul_ceilDiv ha
lemma ceilDiv_le_iff_le_mul (ha : 0 < a) : b ⌈/⌉ a ≤ c ↔ b ≤ a * c := ceilDiv_le_iff_le_smul ha

end CeilDiv
end OrderedSemiring

namespace Nat

instance instFloorDiv : FloorDiv ℕ ℕ where
  floorDiv := HDiv.hDiv
  floorDiv_gc a ha := by simpa [mul_comm] using Nat.galoisConnection_mul_div ha
  floorDiv_nonpos a ha b := by rw [ha.antisymm $ zero_le _, Nat.div_zero]
  zero_floorDiv := Nat.zero_div

instance instCeilDiv : CeilDiv ℕ ℕ where
  ceilDiv a b := (a + b - 1) / b
  ceilDiv_gc a ha b c := by
    simp [div_le_iff_le_mul_add_pred ha, add_assoc, tsub_add_cancel_of_le $ succ_le_iff.2 ha]
  ceilDiv_nonpos a ha b := by simp_rw [ha.antisymm $ zero_le _, Nat.div_zero]
  zero_ceilDiv a := by cases a <;> simp [Nat.div_eq_zero_iff]

@[simp] lemma floorDiv_eq_div (a b : ℕ) : a ⌊/⌋ b = a / b := rfl
lemma ceilDiv_eq_add_pred_div (a b : ℕ) : a ⌈/⌉ b = (a + b - 1) / b := rfl

end Nat

namespace Pi
variable {π : ι → Type*} [OrderedAddCommMonoid α] [∀ i, OrderedAddCommMonoid (π i)]
  [∀ i, SMulZeroClass α (π i)]

section FloorDiv
variable [∀ i, FloorDiv α (π i)]

instance instFloorDiv : FloorDiv α (∀ i, π i) where
  floorDiv f a i := f i ⌊/⌋ a
  floorDiv_gc _a ha _f _g := forall_congr' fun _i ↦ gc_floorDiv_smul ha _ _
  floorDiv_nonpos a ha f := by ext i; exact floorDiv_of_nonpos ha _
  zero_floorDiv a := by ext i; exact zero_floorDiv a

lemma floorDiv_def (f : ∀ i, π i) (a : α) : f ⌊/⌋ a = fun i ↦ f i ⌊/⌋ a := rfl
@[simp] lemma floorDiv_apply (f : ∀ i, π i) (a : α) (i : ι) : (f ⌊/⌋ a) i = f i ⌊/⌋ a := rfl

end FloorDiv

section CeilDiv
variable [∀ i, CeilDiv α (π i)]

instance instCeilDiv : CeilDiv α (∀ i, π i) where
  ceilDiv f a i := f i ⌈/⌉ a
  ceilDiv_gc _a ha _f _g := forall_congr' fun _i ↦ gc_smul_ceilDiv ha _ _
  ceilDiv_nonpos a ha f := by ext i; exact ceilDiv_of_nonpos ha _
  zero_ceilDiv a := by ext; exact zero_ceilDiv _

lemma ceilDiv_def (f : ∀ i, π i) (a : α) : f ⌈/⌉ a = fun i ↦ f i ⌈/⌉ a := rfl
@[simp] lemma ceilDiv_apply (f : ∀ i, π i) (a : α) (i : ι) : (f ⌈/⌉ a) i = f i ⌈/⌉ a := rfl

end CeilDiv
end Pi

namespace Finsupp
variable [OrderedAddCommMonoid α] [OrderedAddCommMonoid β] [SMulZeroClass α β]

section FloorDiv
variable [FloorDiv α β]

noncomputable instance instFloorDiv : FloorDiv α (ι →₀ β) where
  floorDiv f a := f.mapRange (· ⌊/⌋ a) $ zero_floorDiv _
  floorDiv_gc _a ha f _g := forall_congr' fun i ↦ by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_floorDiv_smul ha (f i) _
  floorDiv_nonpos a ha f := by ext i; exact floorDiv_of_nonpos ha _
  zero_floorDiv a := by ext; exact zero_floorDiv _

lemma floorDiv_def (f : ι →₀ β) (a : α) : f ⌊/⌋ a = fun i ↦ f i ⌊/⌋ a := rfl
@[simp] lemma floorDiv_apply (f : ι →₀ β) (a : α) (i : ι) : (f ⌊/⌋ a) i = f i ⌊/⌋ a := rfl

end FloorDiv

section CeilDiv
variable [CeilDiv α β]

noncomputable instance instCeilDiv : CeilDiv α (ι →₀ β) where
  ceilDiv f a := f.mapRange (· ⌈/⌉ a) $ by simp
  ceilDiv_gc _a ha f _g := forall_congr' fun i ↦ by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_smul_ceilDiv ha (f i) _
  ceilDiv_nonpos a ha f := by ext i; exact ceilDiv_of_nonpos ha _
  zero_ceilDiv a := by ext; exact zero_ceilDiv _

lemma ceilDiv_def (f : ι →₀ β) (a : α) : f ⌈/⌉ a = fun i ↦ f i ⌈/⌉ a := rfl
@[simp] lemma ceilDiv_apply (f : ι →₀ β) (a : α) (i : ι) : (f ⌈/⌉ a) i = f i ⌈/⌉ a := rfl

end CeilDiv
end Finsupp

/-- This is the motivating example.-/
noncomputable example : FloorDiv ℕ (ℕ →₀ ℕ) := inferInstance

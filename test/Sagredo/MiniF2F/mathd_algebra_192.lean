import Mathlib.Tactic.GPT.Sagredo.Widget
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Digits

open BigOperators
open Real
open Nat
open Topology

theorem mathd_algebra_192
  (q e d : ℂ)
  (h₀ : q = 11 - (5 * Complex.I))
  (h₁ : e = 11 + (5 * Complex.I))
  (h₂ : d = 2 * Complex.I) :
  q * e * d = 292 * Complex.I := by sagredo
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Pairwise
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

namespace Cover945

/-!
# L1: statement data for the N = 945 CRT capacity certificate

The modulus pool `P(945)` = divisors of `945 = 3^3 * 5 * 7` exceeding 1,
the certificate family `T = {3, 5, 7}`, and the exact rational arithmetic
of the certificate inequality

  `∑ d ∈ P(945) \ T, 1/d = 16/45  <  16/35 = ∏ d ∈ T, (1 - 1/d)`,

i.e. margin `16/35 - 16/45 = 32/315 > 0` (cf. `crt_notes.md` §1, §5).
-/

/-- The modulus pool for `N = 945`: all divisors of 945 exceeding 1. -/
def pool945 : Finset ℕ := {3, 5, 7, 9, 15, 21, 27, 35, 45, 63, 105, 135, 189, 315, 945}

/-- The CRT certificate family `T = {3, 5, 7}` (the distinct prime divisors of 945). -/
def certT : Finset ℕ := {3, 5, 7}

/-- Every element of the pool divides 945 and is at least 2. -/
lemma pool945_dvd {d : ℕ} (h : d ∈ pool945) : d ∣ 945 ∧ 2 ≤ d := by
  fin_cases h <;> exact ⟨by norm_num, by norm_num⟩

/- The pool is complete: every divisor of 945 that is at least 2 lies in it.
   Proved by a decidable check over `d < 946` (kernel computation, no
   `native_decide`, so no extra axioms). -/
set_option maxRecDepth 32768 in
lemma mem_pool945 {d : ℕ} (hdvd : d ∣ 945) (hd : 2 ≤ d) : d ∈ pool945 := by
  have key : ∀ m ∈ Finset.range 946, m ∣ 945 → 2 ≤ m → m ∈ pool945 := by decide
  exact key d (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hdvd))) hdvd hd

/-- The certificate family is contained in the pool. -/
lemma certT_subset_pool945 : certT ⊆ pool945 := by
  intro x hx
  fin_cases hx <;> simp [pool945]

/-- The elements of `T = {3, 5, 7}` are pairwise coprime. -/
lemma certT_pairwise : (certT : Set ℕ).Pairwise Nat.Coprime := by
  intro x hx y hy hxy
  rw [Finset.mem_coe] at hx hy
  fin_cases hx <;> fin_cases hy <;> simp_all <;> norm_num [Nat.Coprime]

/-- The pool minus the certificate family, explicitly. -/
lemma pool945_sdiff_certT :
    pool945 \ certT = {9, 15, 21, 27, 35, 45, 63, 105, 135, 189, 315, 945} := by
  decide

/-- Certificate arithmetic, left side: `∑ d ∈ P(945) \ T, 1/d = 16/45`. -/
lemma cert_sum : ∑ d ∈ pool945 \ certT, (1 : ℚ) / d = 16 / 45 := by
  rw [pool945_sdiff_certT]
  norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- Certificate arithmetic, right side: `∏ d ∈ T, (1 - 1/d) = 16/35`. -/
lemma cert_prod : ∏ d ∈ certT, (1 - (1 : ℚ) / d) = 16 / 35 := by
  norm_num [certT, Finset.prod_insert, Finset.prod_singleton]

/-- The certificate inequality `(★)` for `N = 945`, `T = {3, 5, 7}`:
    `∑ d ∈ P(945) \ T, 1/d < ∏ d ∈ T, (1 - 1/d)`, with margin `32/315`. -/
lemma cert_inequality :
    ∑ d ∈ pool945 \ certT, (1 : ℚ) / d < ∏ d ∈ certT, (1 - (1 : ℚ) / d) := by
  rw [cert_sum, cert_prod]
  norm_num

end Cover945

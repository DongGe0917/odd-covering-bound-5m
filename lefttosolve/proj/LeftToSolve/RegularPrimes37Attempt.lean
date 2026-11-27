import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# L4 (BLOCKED, kept for the record): `¬ IsRegularPrime 37` itself

Source problem (lefttosolve.com, difficulty 16/100): "Infinite Regular
Primes — not isRegularPrime 37". Upstream (formal-conjectures,
`FormalConjectures/Wikipedia/RegularPrimes.lean`) defines

  `IsRegularPrime p : Prop := p.Coprime (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))))`

so the statement below restates it with Mathlib definitions only.
It is a known result (37 is the smallest irregular prime), but a Lean proof
needs one of:
  * Kummer's criterion (the equivalence with Bernoulli numerators), which
    upstream itself lists as a separate theorem "Not in Mathlib"; or
  * a computation of the class number of ℚ(ζ₃₇), for which Mathlib has no
    computational infrastructure.
The `sorry` below is therefore deliberate and documented: this file is
expected to depend on `sorryAx` and does *not* count as a proved result.
The provable computational step (37 ∣ (bernoulli' 32).num) is in
`Bernoulli37.lean`.
-/

open scoped NumberField

/-- Restatement of upstream `RegularPrimes.IsRegularPrime` at p = 37.
    BLOCKED: proof needs Kummer's criterion / class-number computation. -/
theorem not_isRegularPrime_37_attempt :
    ¬ Nat.Coprime 37
      (Fintype.card (ClassGroup (𝓞 (CyclotomicField 37 ℚ)))) := by
  sorry

#print axioms not_isRegularPrime_37_attempt

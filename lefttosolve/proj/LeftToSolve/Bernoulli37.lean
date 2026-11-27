import LeftToSolve.BernoulliValues

/-!
# L1: the Bernoulli computation step behind `not_isRegularPrime_37`

Source problem (lefttosolve.com, difficulty 16/100): "Infinite Regular Primes —
not isRegularPrime 37", a known result (37 is the smallest irregular prime,
irregular pair (37, 32)). The full statement uses the class-group definition
of `IsRegularPrime` and needs Kummer's criterion, which is not in Mathlib, so
the full statement is *not* proved here (see `RegularPrimes37Attempt.lean`).
This file proves the key finite computation (step H1 of the reduction
recorded on the problem page): 37 divides the numerator of `bernoulli' 32`,
via the exact values of `bernoulli' 0, ..., bernoulli' 32` proved in
`BernoulliValues.lean` from the recurrence `bernoulli'_def`.
-/

/-- Exact numerator of `bernoulli' 32` (B₃₂ = -7709321041217 / 510). -/
theorem bernoulli'_32_num : (bernoulli' 32).num = -7709321041217 := by
  rw [bernoulli'_val_32]
  norm_num

/-- The key divisibility: 37 divides the numerator of `bernoulli' 32`
(the irregular pair (37, 32)). -/
theorem dvd_37_bernoulli'_32 : (37 : ℤ) ∣ (bernoulli' 32).num := by
  rw [bernoulli'_32_num]
  norm_num

#print axioms bernoulli'_32_num
#print axioms dvd_37_bernoulli'_32

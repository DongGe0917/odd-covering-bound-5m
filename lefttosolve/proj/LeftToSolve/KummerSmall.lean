import LeftToSolve.BernoulliValues

/-!
# L2: finite instances of the right-hand side of Kummer's criterion

Source problem (lefttosolve.com, difficulty 17/100): "Kummer's criterion",
the known theorem
  `IsRegularPrime p ↔ ∀ k ∈ Finset.Icc 2 (p - 3), Even k → ¬ (p : ℤ) ∣ (bernoulli' k).num`
stated in upstream formal-conjectures (not in Mathlib; the equivalence itself
is *not* proved here). This file verifies the right-hand side, a finite
check, for every regular prime below 37: 5, 7, 11, 13, 17, 19, 23, 29, 31.
Together with `Bernoulli37.lean` (the check fails at p = 37, k = 32), this
covers the complete Kummer-criterion picture for all primes below 37.
-/

/-- Kummer's criterion, right-hand side, at p = 5. -/
theorem kummer_rhs_5 :
    ∀ k ∈ Finset.Icc 2 (5 - 3), Even k → ¬ (5 : ℤ) ∣ (bernoulli' k).num := by
  intro k hk hkE
  rcases hkE with ⟨m, rfl⟩
  simp only [Finset.mem_Icc] at hk
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 1 := by omega
  interval_cases m
  · show ¬ (5 : ℤ) ∣ (bernoulli' 2).num
    rw [bernoulli'_val_2]
    norm_num

#print axioms kummer_rhs_5

/-- Kummer's criterion, right-hand side, at p = 7. -/
theorem kummer_rhs_7 :
    ∀ k ∈ Finset.Icc 2 (7 - 3), Even k → ¬ (7 : ℤ) ∣ (bernoulli' k).num := by
  intro k hk hkE
  rcases hkE with ⟨m, rfl⟩
  simp only [Finset.mem_Icc] at hk
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 2 := by omega
  interval_cases m
  · show ¬ (7 : ℤ) ∣ (bernoulli' 2).num
    rw [bernoulli'_val_2]
    norm_num
  · show ¬ (7 : ℤ) ∣ (bernoulli' 4).num
    rw [bernoulli'_val_4]
    norm_num

#print axioms kummer_rhs_7

/-- Kummer's criterion, right-hand side, at p = 11. -/
theorem kummer_rhs_11 :
    ∀ k ∈ Finset.Icc 2 (11 - 3), Even k → ¬ (11 : ℤ) ∣ (bernoulli' k).num := by
  intro k hk hkE
  rcases hkE with ⟨m, rfl⟩
  simp only [Finset.mem_Icc] at hk
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 4 := by omega
  interval_cases m
  · show ¬ (11 : ℤ) ∣ (bernoulli' 2).num
    rw [bernoulli'_val_2]
    norm_num
  · show ¬ (11 : ℤ) ∣ (bernoulli' 4).num
    rw [bernoulli'_val_4]
    norm_num
  · show ¬ (11 : ℤ) ∣ (bernoulli' 6).num
    rw [bernoulli'_val_6]
    norm_num
  · show ¬ (11 : ℤ) ∣ (bernoulli' 8).num
    rw [bernoulli'_val_8]
    norm_num

#print axioms kummer_rhs_11

/-- Kummer's criterion, right-hand side, at p = 13. -/
theorem kummer_rhs_13 :
    ∀ k ∈ Finset.Icc 2 (13 - 3), Even k → ¬ (13 : ℤ) ∣ (bernoulli' k).num := by
  intro k hk hkE
  rcases hkE with ⟨m, rfl⟩
  simp only [Finset.mem_Icc] at hk
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 5 := by omega
  interval_cases m
  · show ¬ (13 : ℤ) ∣ (bernoulli' 2).num
    rw [bernoulli'_val_2]
    norm_num
  · show ¬ (13 : ℤ) ∣ (bernoulli' 4).num
    rw [bernoulli'_val_4]
    norm_num
  · show ¬ (13 : ℤ) ∣ (bernoulli' 6).num
    rw [bernoulli'_val_6]
    norm_num
  · show ¬ (13 : ℤ) ∣ (bernoulli' 8).num
    rw [bernoulli'_val_8]
    norm_num
  · show ¬ (13 : ℤ) ∣ (bernoulli' 10).num
    rw [bernoulli'_val_10]
    norm_num

#print axioms kummer_rhs_13

/-- Kummer's criterion, right-hand side, at p = 17. -/
theorem kummer_rhs_17 :
    ∀ k ∈ Finset.Icc 2 (17 - 3), Even k → ¬ (17 : ℤ) ∣ (bernoulli' k).num := by
  intro k hk hkE
  rcases hkE with ⟨m, rfl⟩
  simp only [Finset.mem_Icc] at hk
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 7 := by omega
  interval_cases m
  · show ¬ (17 : ℤ) ∣ (bernoulli' 2).num
    rw [bernoulli'_val_2]
    norm_num
  · show ¬ (17 : ℤ) ∣ (bernoulli' 4).num
    rw [bernoulli'_val_4]
    norm_num
  · show ¬ (17 : ℤ) ∣ (bernoulli' 6).num
    rw [bernoulli'_val_6]
    norm_num
  · show ¬ (17 : ℤ) ∣ (bernoulli' 8).num
    rw [bernoulli'_val_8]
    norm_num
  · show ¬ (17 : ℤ) ∣ (bernoulli' 10).num
    rw [bernoulli'_val_10]
    norm_num
  · show ¬ (17 : ℤ) ∣ (bernoulli' 12).num
    rw [bernoulli'_val_12]
    norm_num
  · show ¬ (17 : ℤ) ∣ (bernoulli' 14).num
    rw [bernoulli'_val_14]
    norm_num

#print axioms kummer_rhs_17

/-- Kummer's criterion, right-hand side, at p = 19. -/
theorem kummer_rhs_19 :
    ∀ k ∈ Finset.Icc 2 (19 - 3), Even k → ¬ (19 : ℤ) ∣ (bernoulli' k).num := by
  intro k hk hkE
  rcases hkE with ⟨m, rfl⟩
  simp only [Finset.mem_Icc] at hk
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 8 := by omega
  interval_cases m
  · show ¬ (19 : ℤ) ∣ (bernoulli' 2).num
    rw [bernoulli'_val_2]
    norm_num
  · show ¬ (19 : ℤ) ∣ (bernoulli' 4).num
    rw [bernoulli'_val_4]
    norm_num
  · show ¬ (19 : ℤ) ∣ (bernoulli' 6).num
    rw [bernoulli'_val_6]
    norm_num
  · show ¬ (19 : ℤ) ∣ (bernoulli' 8).num
    rw [bernoulli'_val_8]
    norm_num
  · show ¬ (19 : ℤ) ∣ (bernoulli' 10).num
    rw [bernoulli'_val_10]
    norm_num
  · show ¬ (19 : ℤ) ∣ (bernoulli' 12).num
    rw [bernoulli'_val_12]
    norm_num
  · show ¬ (19 : ℤ) ∣ (bernoulli' 14).num
    rw [bernoulli'_val_14]
    norm_num
  · show ¬ (19 : ℤ) ∣ (bernoulli' 16).num
    rw [bernoulli'_val_16]
    norm_num

#print axioms kummer_rhs_19

/-- Kummer's criterion, right-hand side, at p = 23. -/
theorem kummer_rhs_23 :
    ∀ k ∈ Finset.Icc 2 (23 - 3), Even k → ¬ (23 : ℤ) ∣ (bernoulli' k).num := by
  intro k hk hkE
  rcases hkE with ⟨m, rfl⟩
  simp only [Finset.mem_Icc] at hk
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 10 := by omega
  interval_cases m
  · show ¬ (23 : ℤ) ∣ (bernoulli' 2).num
    rw [bernoulli'_val_2]
    norm_num
  · show ¬ (23 : ℤ) ∣ (bernoulli' 4).num
    rw [bernoulli'_val_4]
    norm_num
  · show ¬ (23 : ℤ) ∣ (bernoulli' 6).num
    rw [bernoulli'_val_6]
    norm_num
  · show ¬ (23 : ℤ) ∣ (bernoulli' 8).num
    rw [bernoulli'_val_8]
    norm_num
  · show ¬ (23 : ℤ) ∣ (bernoulli' 10).num
    rw [bernoulli'_val_10]
    norm_num
  · show ¬ (23 : ℤ) ∣ (bernoulli' 12).num
    rw [bernoulli'_val_12]
    norm_num
  · show ¬ (23 : ℤ) ∣ (bernoulli' 14).num
    rw [bernoulli'_val_14]
    norm_num
  · show ¬ (23 : ℤ) ∣ (bernoulli' 16).num
    rw [bernoulli'_val_16]
    norm_num
  · show ¬ (23 : ℤ) ∣ (bernoulli' 18).num
    rw [bernoulli'_val_18]
    norm_num
  · show ¬ (23 : ℤ) ∣ (bernoulli' 20).num
    rw [bernoulli'_val_20]
    norm_num

#print axioms kummer_rhs_23

/-- Kummer's criterion, right-hand side, at p = 29. -/
theorem kummer_rhs_29 :
    ∀ k ∈ Finset.Icc 2 (29 - 3), Even k → ¬ (29 : ℤ) ∣ (bernoulli' k).num := by
  intro k hk hkE
  rcases hkE with ⟨m, rfl⟩
  simp only [Finset.mem_Icc] at hk
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 13 := by omega
  interval_cases m
  · show ¬ (29 : ℤ) ∣ (bernoulli' 2).num
    rw [bernoulli'_val_2]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 4).num
    rw [bernoulli'_val_4]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 6).num
    rw [bernoulli'_val_6]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 8).num
    rw [bernoulli'_val_8]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 10).num
    rw [bernoulli'_val_10]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 12).num
    rw [bernoulli'_val_12]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 14).num
    rw [bernoulli'_val_14]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 16).num
    rw [bernoulli'_val_16]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 18).num
    rw [bernoulli'_val_18]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 20).num
    rw [bernoulli'_val_20]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 22).num
    rw [bernoulli'_val_22]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 24).num
    rw [bernoulli'_val_24]
    norm_num
  · show ¬ (29 : ℤ) ∣ (bernoulli' 26).num
    rw [bernoulli'_val_26]
    norm_num

#print axioms kummer_rhs_29

/-- Kummer's criterion, right-hand side, at p = 31. -/
theorem kummer_rhs_31 :
    ∀ k ∈ Finset.Icc 2 (31 - 3), Even k → ¬ (31 : ℤ) ∣ (bernoulli' k).num := by
  intro k hk hkE
  rcases hkE with ⟨m, rfl⟩
  simp only [Finset.mem_Icc] at hk
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 14 := by omega
  interval_cases m
  · show ¬ (31 : ℤ) ∣ (bernoulli' 2).num
    rw [bernoulli'_val_2]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 4).num
    rw [bernoulli'_val_4]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 6).num
    rw [bernoulli'_val_6]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 8).num
    rw [bernoulli'_val_8]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 10).num
    rw [bernoulli'_val_10]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 12).num
    rw [bernoulli'_val_12]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 14).num
    rw [bernoulli'_val_14]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 16).num
    rw [bernoulli'_val_16]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 18).num
    rw [bernoulli'_val_18]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 20).num
    rw [bernoulli'_val_20]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 22).num
    rw [bernoulli'_val_22]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 24).num
    rw [bernoulli'_val_24]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 26).num
    rw [bernoulli'_val_26]
    norm_num
  · show ¬ (31 : ℤ) ∣ (bernoulli' 28).num
    rw [bernoulli'_val_28]
    norm_num

#print axioms kummer_rhs_31

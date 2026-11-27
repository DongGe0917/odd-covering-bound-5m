import Mathlib.NumberTheory.Bernoulli

/-! # Bernoulli' values by recurrence (generated)

`Nat.choose` values are proved by Pascal DP lemmas (kernel `decide` on
`Nat.choose 32 16` would be exponential; each DP step is O(1)). -/

theorem choose_val_2_0 : Nat.choose 2 0 = 1 := Nat.choose_zero_right _
theorem choose_val_2_1 : Nat.choose 2 1 = 2 := Nat.choose_one_right _
theorem choose_val_2_2 : Nat.choose 2 2 = 1 := Nat.choose_self _
theorem choose_val_3_0 : Nat.choose 3 0 = 1 := Nat.choose_zero_right _
theorem choose_val_3_1 : Nat.choose 3 1 = 3 := Nat.choose_one_right _
theorem choose_val_3_2 : Nat.choose 3 2 = 3 := by
  rw [Nat.choose_succ_succ, choose_val_2_1, choose_val_2_2]
theorem choose_val_3_3 : Nat.choose 3 3 = 1 := Nat.choose_self _
theorem choose_val_4_0 : Nat.choose 4 0 = 1 := Nat.choose_zero_right _
theorem choose_val_4_1 : Nat.choose 4 1 = 4 := Nat.choose_one_right _
theorem choose_val_4_2 : Nat.choose 4 2 = 6 := by
  rw [Nat.choose_succ_succ, choose_val_3_1, choose_val_3_2]
theorem choose_val_4_3 : Nat.choose 4 3 = 4 := by
  rw [Nat.choose_succ_succ, choose_val_3_2, choose_val_3_3]
theorem choose_val_4_4 : Nat.choose 4 4 = 1 := Nat.choose_self _
theorem choose_val_5_0 : Nat.choose 5 0 = 1 := Nat.choose_zero_right _
theorem choose_val_5_1 : Nat.choose 5 1 = 5 := Nat.choose_one_right _
theorem choose_val_5_2 : Nat.choose 5 2 = 10 := by
  rw [Nat.choose_succ_succ, choose_val_4_1, choose_val_4_2]
theorem choose_val_5_3 : Nat.choose 5 3 = 10 := by
  rw [Nat.choose_succ_succ, choose_val_4_2, choose_val_4_3]
theorem choose_val_5_4 : Nat.choose 5 4 = 5 := by
  rw [Nat.choose_succ_succ, choose_val_4_3, choose_val_4_4]
theorem choose_val_5_5 : Nat.choose 5 5 = 1 := Nat.choose_self _
theorem choose_val_6_0 : Nat.choose 6 0 = 1 := Nat.choose_zero_right _
theorem choose_val_6_1 : Nat.choose 6 1 = 6 := Nat.choose_one_right _
theorem choose_val_6_2 : Nat.choose 6 2 = 15 := by
  rw [Nat.choose_succ_succ, choose_val_5_1, choose_val_5_2]
theorem choose_val_6_3 : Nat.choose 6 3 = 20 := by
  rw [Nat.choose_succ_succ, choose_val_5_2, choose_val_5_3]
theorem choose_val_6_4 : Nat.choose 6 4 = 15 := by
  rw [Nat.choose_succ_succ, choose_val_5_3, choose_val_5_4]
theorem choose_val_6_5 : Nat.choose 6 5 = 6 := by
  rw [Nat.choose_succ_succ, choose_val_5_4, choose_val_5_5]
theorem choose_val_6_6 : Nat.choose 6 6 = 1 := Nat.choose_self _
theorem choose_val_7_0 : Nat.choose 7 0 = 1 := Nat.choose_zero_right _
theorem choose_val_7_1 : Nat.choose 7 1 = 7 := Nat.choose_one_right _
theorem choose_val_7_2 : Nat.choose 7 2 = 21 := by
  rw [Nat.choose_succ_succ, choose_val_6_1, choose_val_6_2]
theorem choose_val_7_3 : Nat.choose 7 3 = 35 := by
  rw [Nat.choose_succ_succ, choose_val_6_2, choose_val_6_3]
theorem choose_val_7_4 : Nat.choose 7 4 = 35 := by
  rw [Nat.choose_succ_succ, choose_val_6_3, choose_val_6_4]
theorem choose_val_7_5 : Nat.choose 7 5 = 21 := by
  rw [Nat.choose_succ_succ, choose_val_6_4, choose_val_6_5]
theorem choose_val_7_6 : Nat.choose 7 6 = 7 := by
  rw [Nat.choose_succ_succ, choose_val_6_5, choose_val_6_6]
theorem choose_val_7_7 : Nat.choose 7 7 = 1 := Nat.choose_self _
theorem choose_val_8_0 : Nat.choose 8 0 = 1 := Nat.choose_zero_right _
theorem choose_val_8_1 : Nat.choose 8 1 = 8 := Nat.choose_one_right _
theorem choose_val_8_2 : Nat.choose 8 2 = 28 := by
  rw [Nat.choose_succ_succ, choose_val_7_1, choose_val_7_2]
theorem choose_val_8_3 : Nat.choose 8 3 = 56 := by
  rw [Nat.choose_succ_succ, choose_val_7_2, choose_val_7_3]
theorem choose_val_8_4 : Nat.choose 8 4 = 70 := by
  rw [Nat.choose_succ_succ, choose_val_7_3, choose_val_7_4]
theorem choose_val_8_5 : Nat.choose 8 5 = 56 := by
  rw [Nat.choose_succ_succ, choose_val_7_4, choose_val_7_5]
theorem choose_val_8_6 : Nat.choose 8 6 = 28 := by
  rw [Nat.choose_succ_succ, choose_val_7_5, choose_val_7_6]
theorem choose_val_8_7 : Nat.choose 8 7 = 8 := by
  rw [Nat.choose_succ_succ, choose_val_7_6, choose_val_7_7]
theorem choose_val_8_8 : Nat.choose 8 8 = 1 := Nat.choose_self _
theorem choose_val_9_0 : Nat.choose 9 0 = 1 := Nat.choose_zero_right _
theorem choose_val_9_1 : Nat.choose 9 1 = 9 := Nat.choose_one_right _
theorem choose_val_9_2 : Nat.choose 9 2 = 36 := by
  rw [Nat.choose_succ_succ, choose_val_8_1, choose_val_8_2]
theorem choose_val_9_3 : Nat.choose 9 3 = 84 := by
  rw [Nat.choose_succ_succ, choose_val_8_2, choose_val_8_3]
theorem choose_val_9_4 : Nat.choose 9 4 = 126 := by
  rw [Nat.choose_succ_succ, choose_val_8_3, choose_val_8_4]
theorem choose_val_9_5 : Nat.choose 9 5 = 126 := by
  rw [Nat.choose_succ_succ, choose_val_8_4, choose_val_8_5]
theorem choose_val_9_6 : Nat.choose 9 6 = 84 := by
  rw [Nat.choose_succ_succ, choose_val_8_5, choose_val_8_6]
theorem choose_val_9_7 : Nat.choose 9 7 = 36 := by
  rw [Nat.choose_succ_succ, choose_val_8_6, choose_val_8_7]
theorem choose_val_9_8 : Nat.choose 9 8 = 9 := by
  rw [Nat.choose_succ_succ, choose_val_8_7, choose_val_8_8]
theorem choose_val_9_9 : Nat.choose 9 9 = 1 := Nat.choose_self _
theorem choose_val_10_0 : Nat.choose 10 0 = 1 := Nat.choose_zero_right _
theorem choose_val_10_1 : Nat.choose 10 1 = 10 := Nat.choose_one_right _
theorem choose_val_10_2 : Nat.choose 10 2 = 45 := by
  rw [Nat.choose_succ_succ, choose_val_9_1, choose_val_9_2]
theorem choose_val_10_3 : Nat.choose 10 3 = 120 := by
  rw [Nat.choose_succ_succ, choose_val_9_2, choose_val_9_3]
theorem choose_val_10_4 : Nat.choose 10 4 = 210 := by
  rw [Nat.choose_succ_succ, choose_val_9_3, choose_val_9_4]
theorem choose_val_10_5 : Nat.choose 10 5 = 252 := by
  rw [Nat.choose_succ_succ, choose_val_9_4, choose_val_9_5]
theorem choose_val_10_6 : Nat.choose 10 6 = 210 := by
  rw [Nat.choose_succ_succ, choose_val_9_5, choose_val_9_6]
theorem choose_val_10_7 : Nat.choose 10 7 = 120 := by
  rw [Nat.choose_succ_succ, choose_val_9_6, choose_val_9_7]
theorem choose_val_10_8 : Nat.choose 10 8 = 45 := by
  rw [Nat.choose_succ_succ, choose_val_9_7, choose_val_9_8]
theorem choose_val_10_9 : Nat.choose 10 9 = 10 := by
  rw [Nat.choose_succ_succ, choose_val_9_8, choose_val_9_9]
theorem choose_val_10_10 : Nat.choose 10 10 = 1 := Nat.choose_self _
theorem choose_val_11_0 : Nat.choose 11 0 = 1 := Nat.choose_zero_right _
theorem choose_val_11_1 : Nat.choose 11 1 = 11 := Nat.choose_one_right _
theorem choose_val_11_2 : Nat.choose 11 2 = 55 := by
  rw [Nat.choose_succ_succ, choose_val_10_1, choose_val_10_2]
theorem choose_val_11_3 : Nat.choose 11 3 = 165 := by
  rw [Nat.choose_succ_succ, choose_val_10_2, choose_val_10_3]
theorem choose_val_11_4 : Nat.choose 11 4 = 330 := by
  rw [Nat.choose_succ_succ, choose_val_10_3, choose_val_10_4]
theorem choose_val_11_5 : Nat.choose 11 5 = 462 := by
  rw [Nat.choose_succ_succ, choose_val_10_4, choose_val_10_5]
theorem choose_val_11_6 : Nat.choose 11 6 = 462 := by
  rw [Nat.choose_succ_succ, choose_val_10_5, choose_val_10_6]
theorem choose_val_11_7 : Nat.choose 11 7 = 330 := by
  rw [Nat.choose_succ_succ, choose_val_10_6, choose_val_10_7]
theorem choose_val_11_8 : Nat.choose 11 8 = 165 := by
  rw [Nat.choose_succ_succ, choose_val_10_7, choose_val_10_8]
theorem choose_val_11_9 : Nat.choose 11 9 = 55 := by
  rw [Nat.choose_succ_succ, choose_val_10_8, choose_val_10_9]
theorem choose_val_11_10 : Nat.choose 11 10 = 11 := by
  rw [Nat.choose_succ_succ, choose_val_10_9, choose_val_10_10]
theorem choose_val_11_11 : Nat.choose 11 11 = 1 := Nat.choose_self _
theorem choose_val_12_0 : Nat.choose 12 0 = 1 := Nat.choose_zero_right _
theorem choose_val_12_1 : Nat.choose 12 1 = 12 := Nat.choose_one_right _
theorem choose_val_12_2 : Nat.choose 12 2 = 66 := by
  rw [Nat.choose_succ_succ, choose_val_11_1, choose_val_11_2]
theorem choose_val_12_3 : Nat.choose 12 3 = 220 := by
  rw [Nat.choose_succ_succ, choose_val_11_2, choose_val_11_3]
theorem choose_val_12_4 : Nat.choose 12 4 = 495 := by
  rw [Nat.choose_succ_succ, choose_val_11_3, choose_val_11_4]
theorem choose_val_12_5 : Nat.choose 12 5 = 792 := by
  rw [Nat.choose_succ_succ, choose_val_11_4, choose_val_11_5]
theorem choose_val_12_6 : Nat.choose 12 6 = 924 := by
  rw [Nat.choose_succ_succ, choose_val_11_5, choose_val_11_6]
theorem choose_val_12_7 : Nat.choose 12 7 = 792 := by
  rw [Nat.choose_succ_succ, choose_val_11_6, choose_val_11_7]
theorem choose_val_12_8 : Nat.choose 12 8 = 495 := by
  rw [Nat.choose_succ_succ, choose_val_11_7, choose_val_11_8]
theorem choose_val_12_9 : Nat.choose 12 9 = 220 := by
  rw [Nat.choose_succ_succ, choose_val_11_8, choose_val_11_9]
theorem choose_val_12_10 : Nat.choose 12 10 = 66 := by
  rw [Nat.choose_succ_succ, choose_val_11_9, choose_val_11_10]
theorem choose_val_12_11 : Nat.choose 12 11 = 12 := by
  rw [Nat.choose_succ_succ, choose_val_11_10, choose_val_11_11]
theorem choose_val_12_12 : Nat.choose 12 12 = 1 := Nat.choose_self _
theorem choose_val_13_0 : Nat.choose 13 0 = 1 := Nat.choose_zero_right _
theorem choose_val_13_1 : Nat.choose 13 1 = 13 := Nat.choose_one_right _
theorem choose_val_13_2 : Nat.choose 13 2 = 78 := by
  rw [Nat.choose_succ_succ, choose_val_12_1, choose_val_12_2]
theorem choose_val_13_3 : Nat.choose 13 3 = 286 := by
  rw [Nat.choose_succ_succ, choose_val_12_2, choose_val_12_3]
theorem choose_val_13_4 : Nat.choose 13 4 = 715 := by
  rw [Nat.choose_succ_succ, choose_val_12_3, choose_val_12_4]
theorem choose_val_13_5 : Nat.choose 13 5 = 1287 := by
  rw [Nat.choose_succ_succ, choose_val_12_4, choose_val_12_5]
theorem choose_val_13_6 : Nat.choose 13 6 = 1716 := by
  rw [Nat.choose_succ_succ, choose_val_12_5, choose_val_12_6]
theorem choose_val_13_7 : Nat.choose 13 7 = 1716 := by
  rw [Nat.choose_succ_succ, choose_val_12_6, choose_val_12_7]
theorem choose_val_13_8 : Nat.choose 13 8 = 1287 := by
  rw [Nat.choose_succ_succ, choose_val_12_7, choose_val_12_8]
theorem choose_val_13_9 : Nat.choose 13 9 = 715 := by
  rw [Nat.choose_succ_succ, choose_val_12_8, choose_val_12_9]
theorem choose_val_13_10 : Nat.choose 13 10 = 286 := by
  rw [Nat.choose_succ_succ, choose_val_12_9, choose_val_12_10]
theorem choose_val_13_11 : Nat.choose 13 11 = 78 := by
  rw [Nat.choose_succ_succ, choose_val_12_10, choose_val_12_11]
theorem choose_val_13_12 : Nat.choose 13 12 = 13 := by
  rw [Nat.choose_succ_succ, choose_val_12_11, choose_val_12_12]
theorem choose_val_13_13 : Nat.choose 13 13 = 1 := Nat.choose_self _
theorem choose_val_14_0 : Nat.choose 14 0 = 1 := Nat.choose_zero_right _
theorem choose_val_14_1 : Nat.choose 14 1 = 14 := Nat.choose_one_right _
theorem choose_val_14_2 : Nat.choose 14 2 = 91 := by
  rw [Nat.choose_succ_succ, choose_val_13_1, choose_val_13_2]
theorem choose_val_14_3 : Nat.choose 14 3 = 364 := by
  rw [Nat.choose_succ_succ, choose_val_13_2, choose_val_13_3]
theorem choose_val_14_4 : Nat.choose 14 4 = 1001 := by
  rw [Nat.choose_succ_succ, choose_val_13_3, choose_val_13_4]
theorem choose_val_14_5 : Nat.choose 14 5 = 2002 := by
  rw [Nat.choose_succ_succ, choose_val_13_4, choose_val_13_5]
theorem choose_val_14_6 : Nat.choose 14 6 = 3003 := by
  rw [Nat.choose_succ_succ, choose_val_13_5, choose_val_13_6]
theorem choose_val_14_7 : Nat.choose 14 7 = 3432 := by
  rw [Nat.choose_succ_succ, choose_val_13_6, choose_val_13_7]
theorem choose_val_14_8 : Nat.choose 14 8 = 3003 := by
  rw [Nat.choose_succ_succ, choose_val_13_7, choose_val_13_8]
theorem choose_val_14_9 : Nat.choose 14 9 = 2002 := by
  rw [Nat.choose_succ_succ, choose_val_13_8, choose_val_13_9]
theorem choose_val_14_10 : Nat.choose 14 10 = 1001 := by
  rw [Nat.choose_succ_succ, choose_val_13_9, choose_val_13_10]
theorem choose_val_14_11 : Nat.choose 14 11 = 364 := by
  rw [Nat.choose_succ_succ, choose_val_13_10, choose_val_13_11]
theorem choose_val_14_12 : Nat.choose 14 12 = 91 := by
  rw [Nat.choose_succ_succ, choose_val_13_11, choose_val_13_12]
theorem choose_val_14_13 : Nat.choose 14 13 = 14 := by
  rw [Nat.choose_succ_succ, choose_val_13_12, choose_val_13_13]
theorem choose_val_14_14 : Nat.choose 14 14 = 1 := Nat.choose_self _
theorem choose_val_15_0 : Nat.choose 15 0 = 1 := Nat.choose_zero_right _
theorem choose_val_15_1 : Nat.choose 15 1 = 15 := Nat.choose_one_right _
theorem choose_val_15_2 : Nat.choose 15 2 = 105 := by
  rw [Nat.choose_succ_succ, choose_val_14_1, choose_val_14_2]
theorem choose_val_15_3 : Nat.choose 15 3 = 455 := by
  rw [Nat.choose_succ_succ, choose_val_14_2, choose_val_14_3]
theorem choose_val_15_4 : Nat.choose 15 4 = 1365 := by
  rw [Nat.choose_succ_succ, choose_val_14_3, choose_val_14_4]
theorem choose_val_15_5 : Nat.choose 15 5 = 3003 := by
  rw [Nat.choose_succ_succ, choose_val_14_4, choose_val_14_5]
theorem choose_val_15_6 : Nat.choose 15 6 = 5005 := by
  rw [Nat.choose_succ_succ, choose_val_14_5, choose_val_14_6]
theorem choose_val_15_7 : Nat.choose 15 7 = 6435 := by
  rw [Nat.choose_succ_succ, choose_val_14_6, choose_val_14_7]
theorem choose_val_15_8 : Nat.choose 15 8 = 6435 := by
  rw [Nat.choose_succ_succ, choose_val_14_7, choose_val_14_8]
theorem choose_val_15_9 : Nat.choose 15 9 = 5005 := by
  rw [Nat.choose_succ_succ, choose_val_14_8, choose_val_14_9]
theorem choose_val_15_10 : Nat.choose 15 10 = 3003 := by
  rw [Nat.choose_succ_succ, choose_val_14_9, choose_val_14_10]
theorem choose_val_15_11 : Nat.choose 15 11 = 1365 := by
  rw [Nat.choose_succ_succ, choose_val_14_10, choose_val_14_11]
theorem choose_val_15_12 : Nat.choose 15 12 = 455 := by
  rw [Nat.choose_succ_succ, choose_val_14_11, choose_val_14_12]
theorem choose_val_15_13 : Nat.choose 15 13 = 105 := by
  rw [Nat.choose_succ_succ, choose_val_14_12, choose_val_14_13]
theorem choose_val_15_14 : Nat.choose 15 14 = 15 := by
  rw [Nat.choose_succ_succ, choose_val_14_13, choose_val_14_14]
theorem choose_val_15_15 : Nat.choose 15 15 = 1 := Nat.choose_self _
theorem choose_val_16_0 : Nat.choose 16 0 = 1 := Nat.choose_zero_right _
theorem choose_val_16_1 : Nat.choose 16 1 = 16 := Nat.choose_one_right _
theorem choose_val_16_2 : Nat.choose 16 2 = 120 := by
  rw [Nat.choose_succ_succ, choose_val_15_1, choose_val_15_2]
theorem choose_val_16_3 : Nat.choose 16 3 = 560 := by
  rw [Nat.choose_succ_succ, choose_val_15_2, choose_val_15_3]
theorem choose_val_16_4 : Nat.choose 16 4 = 1820 := by
  rw [Nat.choose_succ_succ, choose_val_15_3, choose_val_15_4]
theorem choose_val_16_5 : Nat.choose 16 5 = 4368 := by
  rw [Nat.choose_succ_succ, choose_val_15_4, choose_val_15_5]
theorem choose_val_16_6 : Nat.choose 16 6 = 8008 := by
  rw [Nat.choose_succ_succ, choose_val_15_5, choose_val_15_6]
theorem choose_val_16_7 : Nat.choose 16 7 = 11440 := by
  rw [Nat.choose_succ_succ, choose_val_15_6, choose_val_15_7]
theorem choose_val_16_8 : Nat.choose 16 8 = 12870 := by
  rw [Nat.choose_succ_succ, choose_val_15_7, choose_val_15_8]
theorem choose_val_16_9 : Nat.choose 16 9 = 11440 := by
  rw [Nat.choose_succ_succ, choose_val_15_8, choose_val_15_9]
theorem choose_val_16_10 : Nat.choose 16 10 = 8008 := by
  rw [Nat.choose_succ_succ, choose_val_15_9, choose_val_15_10]
theorem choose_val_16_11 : Nat.choose 16 11 = 4368 := by
  rw [Nat.choose_succ_succ, choose_val_15_10, choose_val_15_11]
theorem choose_val_16_12 : Nat.choose 16 12 = 1820 := by
  rw [Nat.choose_succ_succ, choose_val_15_11, choose_val_15_12]
theorem choose_val_16_13 : Nat.choose 16 13 = 560 := by
  rw [Nat.choose_succ_succ, choose_val_15_12, choose_val_15_13]
theorem choose_val_16_14 : Nat.choose 16 14 = 120 := by
  rw [Nat.choose_succ_succ, choose_val_15_13, choose_val_15_14]
theorem choose_val_16_15 : Nat.choose 16 15 = 16 := by
  rw [Nat.choose_succ_succ, choose_val_15_14, choose_val_15_15]
theorem choose_val_16_16 : Nat.choose 16 16 = 1 := Nat.choose_self _
theorem choose_val_17_0 : Nat.choose 17 0 = 1 := Nat.choose_zero_right _
theorem choose_val_17_1 : Nat.choose 17 1 = 17 := Nat.choose_one_right _
theorem choose_val_17_2 : Nat.choose 17 2 = 136 := by
  rw [Nat.choose_succ_succ, choose_val_16_1, choose_val_16_2]
theorem choose_val_17_3 : Nat.choose 17 3 = 680 := by
  rw [Nat.choose_succ_succ, choose_val_16_2, choose_val_16_3]
theorem choose_val_17_4 : Nat.choose 17 4 = 2380 := by
  rw [Nat.choose_succ_succ, choose_val_16_3, choose_val_16_4]
theorem choose_val_17_5 : Nat.choose 17 5 = 6188 := by
  rw [Nat.choose_succ_succ, choose_val_16_4, choose_val_16_5]
theorem choose_val_17_6 : Nat.choose 17 6 = 12376 := by
  rw [Nat.choose_succ_succ, choose_val_16_5, choose_val_16_6]
theorem choose_val_17_7 : Nat.choose 17 7 = 19448 := by
  rw [Nat.choose_succ_succ, choose_val_16_6, choose_val_16_7]
theorem choose_val_17_8 : Nat.choose 17 8 = 24310 := by
  rw [Nat.choose_succ_succ, choose_val_16_7, choose_val_16_8]
theorem choose_val_17_9 : Nat.choose 17 9 = 24310 := by
  rw [Nat.choose_succ_succ, choose_val_16_8, choose_val_16_9]
theorem choose_val_17_10 : Nat.choose 17 10 = 19448 := by
  rw [Nat.choose_succ_succ, choose_val_16_9, choose_val_16_10]
theorem choose_val_17_11 : Nat.choose 17 11 = 12376 := by
  rw [Nat.choose_succ_succ, choose_val_16_10, choose_val_16_11]
theorem choose_val_17_12 : Nat.choose 17 12 = 6188 := by
  rw [Nat.choose_succ_succ, choose_val_16_11, choose_val_16_12]
theorem choose_val_17_13 : Nat.choose 17 13 = 2380 := by
  rw [Nat.choose_succ_succ, choose_val_16_12, choose_val_16_13]
theorem choose_val_17_14 : Nat.choose 17 14 = 680 := by
  rw [Nat.choose_succ_succ, choose_val_16_13, choose_val_16_14]
theorem choose_val_17_15 : Nat.choose 17 15 = 136 := by
  rw [Nat.choose_succ_succ, choose_val_16_14, choose_val_16_15]
theorem choose_val_17_16 : Nat.choose 17 16 = 17 := by
  rw [Nat.choose_succ_succ, choose_val_16_15, choose_val_16_16]
theorem choose_val_17_17 : Nat.choose 17 17 = 1 := Nat.choose_self _
theorem choose_val_18_0 : Nat.choose 18 0 = 1 := Nat.choose_zero_right _
theorem choose_val_18_1 : Nat.choose 18 1 = 18 := Nat.choose_one_right _
theorem choose_val_18_2 : Nat.choose 18 2 = 153 := by
  rw [Nat.choose_succ_succ, choose_val_17_1, choose_val_17_2]
theorem choose_val_18_3 : Nat.choose 18 3 = 816 := by
  rw [Nat.choose_succ_succ, choose_val_17_2, choose_val_17_3]
theorem choose_val_18_4 : Nat.choose 18 4 = 3060 := by
  rw [Nat.choose_succ_succ, choose_val_17_3, choose_val_17_4]
theorem choose_val_18_5 : Nat.choose 18 5 = 8568 := by
  rw [Nat.choose_succ_succ, choose_val_17_4, choose_val_17_5]
theorem choose_val_18_6 : Nat.choose 18 6 = 18564 := by
  rw [Nat.choose_succ_succ, choose_val_17_5, choose_val_17_6]
theorem choose_val_18_7 : Nat.choose 18 7 = 31824 := by
  rw [Nat.choose_succ_succ, choose_val_17_6, choose_val_17_7]
theorem choose_val_18_8 : Nat.choose 18 8 = 43758 := by
  rw [Nat.choose_succ_succ, choose_val_17_7, choose_val_17_8]
theorem choose_val_18_9 : Nat.choose 18 9 = 48620 := by
  rw [Nat.choose_succ_succ, choose_val_17_8, choose_val_17_9]
theorem choose_val_18_10 : Nat.choose 18 10 = 43758 := by
  rw [Nat.choose_succ_succ, choose_val_17_9, choose_val_17_10]
theorem choose_val_18_11 : Nat.choose 18 11 = 31824 := by
  rw [Nat.choose_succ_succ, choose_val_17_10, choose_val_17_11]
theorem choose_val_18_12 : Nat.choose 18 12 = 18564 := by
  rw [Nat.choose_succ_succ, choose_val_17_11, choose_val_17_12]
theorem choose_val_18_13 : Nat.choose 18 13 = 8568 := by
  rw [Nat.choose_succ_succ, choose_val_17_12, choose_val_17_13]
theorem choose_val_18_14 : Nat.choose 18 14 = 3060 := by
  rw [Nat.choose_succ_succ, choose_val_17_13, choose_val_17_14]
theorem choose_val_18_15 : Nat.choose 18 15 = 816 := by
  rw [Nat.choose_succ_succ, choose_val_17_14, choose_val_17_15]
theorem choose_val_18_16 : Nat.choose 18 16 = 153 := by
  rw [Nat.choose_succ_succ, choose_val_17_15, choose_val_17_16]
theorem choose_val_18_17 : Nat.choose 18 17 = 18 := by
  rw [Nat.choose_succ_succ, choose_val_17_16, choose_val_17_17]
theorem choose_val_18_18 : Nat.choose 18 18 = 1 := Nat.choose_self _
theorem choose_val_19_0 : Nat.choose 19 0 = 1 := Nat.choose_zero_right _
theorem choose_val_19_1 : Nat.choose 19 1 = 19 := Nat.choose_one_right _
theorem choose_val_19_2 : Nat.choose 19 2 = 171 := by
  rw [Nat.choose_succ_succ, choose_val_18_1, choose_val_18_2]
theorem choose_val_19_3 : Nat.choose 19 3 = 969 := by
  rw [Nat.choose_succ_succ, choose_val_18_2, choose_val_18_3]
theorem choose_val_19_4 : Nat.choose 19 4 = 3876 := by
  rw [Nat.choose_succ_succ, choose_val_18_3, choose_val_18_4]
theorem choose_val_19_5 : Nat.choose 19 5 = 11628 := by
  rw [Nat.choose_succ_succ, choose_val_18_4, choose_val_18_5]
theorem choose_val_19_6 : Nat.choose 19 6 = 27132 := by
  rw [Nat.choose_succ_succ, choose_val_18_5, choose_val_18_6]
theorem choose_val_19_7 : Nat.choose 19 7 = 50388 := by
  rw [Nat.choose_succ_succ, choose_val_18_6, choose_val_18_7]
theorem choose_val_19_8 : Nat.choose 19 8 = 75582 := by
  rw [Nat.choose_succ_succ, choose_val_18_7, choose_val_18_8]
theorem choose_val_19_9 : Nat.choose 19 9 = 92378 := by
  rw [Nat.choose_succ_succ, choose_val_18_8, choose_val_18_9]
theorem choose_val_19_10 : Nat.choose 19 10 = 92378 := by
  rw [Nat.choose_succ_succ, choose_val_18_9, choose_val_18_10]
theorem choose_val_19_11 : Nat.choose 19 11 = 75582 := by
  rw [Nat.choose_succ_succ, choose_val_18_10, choose_val_18_11]
theorem choose_val_19_12 : Nat.choose 19 12 = 50388 := by
  rw [Nat.choose_succ_succ, choose_val_18_11, choose_val_18_12]
theorem choose_val_19_13 : Nat.choose 19 13 = 27132 := by
  rw [Nat.choose_succ_succ, choose_val_18_12, choose_val_18_13]
theorem choose_val_19_14 : Nat.choose 19 14 = 11628 := by
  rw [Nat.choose_succ_succ, choose_val_18_13, choose_val_18_14]
theorem choose_val_19_15 : Nat.choose 19 15 = 3876 := by
  rw [Nat.choose_succ_succ, choose_val_18_14, choose_val_18_15]
theorem choose_val_19_16 : Nat.choose 19 16 = 969 := by
  rw [Nat.choose_succ_succ, choose_val_18_15, choose_val_18_16]
theorem choose_val_19_17 : Nat.choose 19 17 = 171 := by
  rw [Nat.choose_succ_succ, choose_val_18_16, choose_val_18_17]
theorem choose_val_19_18 : Nat.choose 19 18 = 19 := by
  rw [Nat.choose_succ_succ, choose_val_18_17, choose_val_18_18]
theorem choose_val_19_19 : Nat.choose 19 19 = 1 := Nat.choose_self _
theorem choose_val_20_0 : Nat.choose 20 0 = 1 := Nat.choose_zero_right _
theorem choose_val_20_1 : Nat.choose 20 1 = 20 := Nat.choose_one_right _
theorem choose_val_20_2 : Nat.choose 20 2 = 190 := by
  rw [Nat.choose_succ_succ, choose_val_19_1, choose_val_19_2]
theorem choose_val_20_3 : Nat.choose 20 3 = 1140 := by
  rw [Nat.choose_succ_succ, choose_val_19_2, choose_val_19_3]
theorem choose_val_20_4 : Nat.choose 20 4 = 4845 := by
  rw [Nat.choose_succ_succ, choose_val_19_3, choose_val_19_4]
theorem choose_val_20_5 : Nat.choose 20 5 = 15504 := by
  rw [Nat.choose_succ_succ, choose_val_19_4, choose_val_19_5]
theorem choose_val_20_6 : Nat.choose 20 6 = 38760 := by
  rw [Nat.choose_succ_succ, choose_val_19_5, choose_val_19_6]
theorem choose_val_20_7 : Nat.choose 20 7 = 77520 := by
  rw [Nat.choose_succ_succ, choose_val_19_6, choose_val_19_7]
theorem choose_val_20_8 : Nat.choose 20 8 = 125970 := by
  rw [Nat.choose_succ_succ, choose_val_19_7, choose_val_19_8]
theorem choose_val_20_9 : Nat.choose 20 9 = 167960 := by
  rw [Nat.choose_succ_succ, choose_val_19_8, choose_val_19_9]
theorem choose_val_20_10 : Nat.choose 20 10 = 184756 := by
  rw [Nat.choose_succ_succ, choose_val_19_9, choose_val_19_10]
theorem choose_val_20_11 : Nat.choose 20 11 = 167960 := by
  rw [Nat.choose_succ_succ, choose_val_19_10, choose_val_19_11]
theorem choose_val_20_12 : Nat.choose 20 12 = 125970 := by
  rw [Nat.choose_succ_succ, choose_val_19_11, choose_val_19_12]
theorem choose_val_20_13 : Nat.choose 20 13 = 77520 := by
  rw [Nat.choose_succ_succ, choose_val_19_12, choose_val_19_13]
theorem choose_val_20_14 : Nat.choose 20 14 = 38760 := by
  rw [Nat.choose_succ_succ, choose_val_19_13, choose_val_19_14]
theorem choose_val_20_15 : Nat.choose 20 15 = 15504 := by
  rw [Nat.choose_succ_succ, choose_val_19_14, choose_val_19_15]
theorem choose_val_20_16 : Nat.choose 20 16 = 4845 := by
  rw [Nat.choose_succ_succ, choose_val_19_15, choose_val_19_16]
theorem choose_val_20_17 : Nat.choose 20 17 = 1140 := by
  rw [Nat.choose_succ_succ, choose_val_19_16, choose_val_19_17]
theorem choose_val_20_18 : Nat.choose 20 18 = 190 := by
  rw [Nat.choose_succ_succ, choose_val_19_17, choose_val_19_18]
theorem choose_val_20_19 : Nat.choose 20 19 = 20 := by
  rw [Nat.choose_succ_succ, choose_val_19_18, choose_val_19_19]
theorem choose_val_20_20 : Nat.choose 20 20 = 1 := Nat.choose_self _
theorem choose_val_21_0 : Nat.choose 21 0 = 1 := Nat.choose_zero_right _
theorem choose_val_21_1 : Nat.choose 21 1 = 21 := Nat.choose_one_right _
theorem choose_val_21_2 : Nat.choose 21 2 = 210 := by
  rw [Nat.choose_succ_succ, choose_val_20_1, choose_val_20_2]
theorem choose_val_21_3 : Nat.choose 21 3 = 1330 := by
  rw [Nat.choose_succ_succ, choose_val_20_2, choose_val_20_3]
theorem choose_val_21_4 : Nat.choose 21 4 = 5985 := by
  rw [Nat.choose_succ_succ, choose_val_20_3, choose_val_20_4]
theorem choose_val_21_5 : Nat.choose 21 5 = 20349 := by
  rw [Nat.choose_succ_succ, choose_val_20_4, choose_val_20_5]
theorem choose_val_21_6 : Nat.choose 21 6 = 54264 := by
  rw [Nat.choose_succ_succ, choose_val_20_5, choose_val_20_6]
theorem choose_val_21_7 : Nat.choose 21 7 = 116280 := by
  rw [Nat.choose_succ_succ, choose_val_20_6, choose_val_20_7]
theorem choose_val_21_8 : Nat.choose 21 8 = 203490 := by
  rw [Nat.choose_succ_succ, choose_val_20_7, choose_val_20_8]
theorem choose_val_21_9 : Nat.choose 21 9 = 293930 := by
  rw [Nat.choose_succ_succ, choose_val_20_8, choose_val_20_9]
theorem choose_val_21_10 : Nat.choose 21 10 = 352716 := by
  rw [Nat.choose_succ_succ, choose_val_20_9, choose_val_20_10]
theorem choose_val_21_11 : Nat.choose 21 11 = 352716 := by
  rw [Nat.choose_succ_succ, choose_val_20_10, choose_val_20_11]
theorem choose_val_21_12 : Nat.choose 21 12 = 293930 := by
  rw [Nat.choose_succ_succ, choose_val_20_11, choose_val_20_12]
theorem choose_val_21_13 : Nat.choose 21 13 = 203490 := by
  rw [Nat.choose_succ_succ, choose_val_20_12, choose_val_20_13]
theorem choose_val_21_14 : Nat.choose 21 14 = 116280 := by
  rw [Nat.choose_succ_succ, choose_val_20_13, choose_val_20_14]
theorem choose_val_21_15 : Nat.choose 21 15 = 54264 := by
  rw [Nat.choose_succ_succ, choose_val_20_14, choose_val_20_15]
theorem choose_val_21_16 : Nat.choose 21 16 = 20349 := by
  rw [Nat.choose_succ_succ, choose_val_20_15, choose_val_20_16]
theorem choose_val_21_17 : Nat.choose 21 17 = 5985 := by
  rw [Nat.choose_succ_succ, choose_val_20_16, choose_val_20_17]
theorem choose_val_21_18 : Nat.choose 21 18 = 1330 := by
  rw [Nat.choose_succ_succ, choose_val_20_17, choose_val_20_18]
theorem choose_val_21_19 : Nat.choose 21 19 = 210 := by
  rw [Nat.choose_succ_succ, choose_val_20_18, choose_val_20_19]
theorem choose_val_21_20 : Nat.choose 21 20 = 21 := by
  rw [Nat.choose_succ_succ, choose_val_20_19, choose_val_20_20]
theorem choose_val_21_21 : Nat.choose 21 21 = 1 := Nat.choose_self _
theorem choose_val_22_0 : Nat.choose 22 0 = 1 := Nat.choose_zero_right _
theorem choose_val_22_1 : Nat.choose 22 1 = 22 := Nat.choose_one_right _
theorem choose_val_22_2 : Nat.choose 22 2 = 231 := by
  rw [Nat.choose_succ_succ, choose_val_21_1, choose_val_21_2]
theorem choose_val_22_3 : Nat.choose 22 3 = 1540 := by
  rw [Nat.choose_succ_succ, choose_val_21_2, choose_val_21_3]
theorem choose_val_22_4 : Nat.choose 22 4 = 7315 := by
  rw [Nat.choose_succ_succ, choose_val_21_3, choose_val_21_4]
theorem choose_val_22_5 : Nat.choose 22 5 = 26334 := by
  rw [Nat.choose_succ_succ, choose_val_21_4, choose_val_21_5]
theorem choose_val_22_6 : Nat.choose 22 6 = 74613 := by
  rw [Nat.choose_succ_succ, choose_val_21_5, choose_val_21_6]
theorem choose_val_22_7 : Nat.choose 22 7 = 170544 := by
  rw [Nat.choose_succ_succ, choose_val_21_6, choose_val_21_7]
theorem choose_val_22_8 : Nat.choose 22 8 = 319770 := by
  rw [Nat.choose_succ_succ, choose_val_21_7, choose_val_21_8]
theorem choose_val_22_9 : Nat.choose 22 9 = 497420 := by
  rw [Nat.choose_succ_succ, choose_val_21_8, choose_val_21_9]
theorem choose_val_22_10 : Nat.choose 22 10 = 646646 := by
  rw [Nat.choose_succ_succ, choose_val_21_9, choose_val_21_10]
theorem choose_val_22_11 : Nat.choose 22 11 = 705432 := by
  rw [Nat.choose_succ_succ, choose_val_21_10, choose_val_21_11]
theorem choose_val_22_12 : Nat.choose 22 12 = 646646 := by
  rw [Nat.choose_succ_succ, choose_val_21_11, choose_val_21_12]
theorem choose_val_22_13 : Nat.choose 22 13 = 497420 := by
  rw [Nat.choose_succ_succ, choose_val_21_12, choose_val_21_13]
theorem choose_val_22_14 : Nat.choose 22 14 = 319770 := by
  rw [Nat.choose_succ_succ, choose_val_21_13, choose_val_21_14]
theorem choose_val_22_15 : Nat.choose 22 15 = 170544 := by
  rw [Nat.choose_succ_succ, choose_val_21_14, choose_val_21_15]
theorem choose_val_22_16 : Nat.choose 22 16 = 74613 := by
  rw [Nat.choose_succ_succ, choose_val_21_15, choose_val_21_16]
theorem choose_val_22_17 : Nat.choose 22 17 = 26334 := by
  rw [Nat.choose_succ_succ, choose_val_21_16, choose_val_21_17]
theorem choose_val_22_18 : Nat.choose 22 18 = 7315 := by
  rw [Nat.choose_succ_succ, choose_val_21_17, choose_val_21_18]
theorem choose_val_22_19 : Nat.choose 22 19 = 1540 := by
  rw [Nat.choose_succ_succ, choose_val_21_18, choose_val_21_19]
theorem choose_val_22_20 : Nat.choose 22 20 = 231 := by
  rw [Nat.choose_succ_succ, choose_val_21_19, choose_val_21_20]
theorem choose_val_22_21 : Nat.choose 22 21 = 22 := by
  rw [Nat.choose_succ_succ, choose_val_21_20, choose_val_21_21]
theorem choose_val_22_22 : Nat.choose 22 22 = 1 := Nat.choose_self _
theorem choose_val_23_0 : Nat.choose 23 0 = 1 := Nat.choose_zero_right _
theorem choose_val_23_1 : Nat.choose 23 1 = 23 := Nat.choose_one_right _
theorem choose_val_23_2 : Nat.choose 23 2 = 253 := by
  rw [Nat.choose_succ_succ, choose_val_22_1, choose_val_22_2]
theorem choose_val_23_3 : Nat.choose 23 3 = 1771 := by
  rw [Nat.choose_succ_succ, choose_val_22_2, choose_val_22_3]
theorem choose_val_23_4 : Nat.choose 23 4 = 8855 := by
  rw [Nat.choose_succ_succ, choose_val_22_3, choose_val_22_4]
theorem choose_val_23_5 : Nat.choose 23 5 = 33649 := by
  rw [Nat.choose_succ_succ, choose_val_22_4, choose_val_22_5]
theorem choose_val_23_6 : Nat.choose 23 6 = 100947 := by
  rw [Nat.choose_succ_succ, choose_val_22_5, choose_val_22_6]
theorem choose_val_23_7 : Nat.choose 23 7 = 245157 := by
  rw [Nat.choose_succ_succ, choose_val_22_6, choose_val_22_7]
theorem choose_val_23_8 : Nat.choose 23 8 = 490314 := by
  rw [Nat.choose_succ_succ, choose_val_22_7, choose_val_22_8]
theorem choose_val_23_9 : Nat.choose 23 9 = 817190 := by
  rw [Nat.choose_succ_succ, choose_val_22_8, choose_val_22_9]
theorem choose_val_23_10 : Nat.choose 23 10 = 1144066 := by
  rw [Nat.choose_succ_succ, choose_val_22_9, choose_val_22_10]
theorem choose_val_23_11 : Nat.choose 23 11 = 1352078 := by
  rw [Nat.choose_succ_succ, choose_val_22_10, choose_val_22_11]
theorem choose_val_23_12 : Nat.choose 23 12 = 1352078 := by
  rw [Nat.choose_succ_succ, choose_val_22_11, choose_val_22_12]
theorem choose_val_23_13 : Nat.choose 23 13 = 1144066 := by
  rw [Nat.choose_succ_succ, choose_val_22_12, choose_val_22_13]
theorem choose_val_23_14 : Nat.choose 23 14 = 817190 := by
  rw [Nat.choose_succ_succ, choose_val_22_13, choose_val_22_14]
theorem choose_val_23_15 : Nat.choose 23 15 = 490314 := by
  rw [Nat.choose_succ_succ, choose_val_22_14, choose_val_22_15]
theorem choose_val_23_16 : Nat.choose 23 16 = 245157 := by
  rw [Nat.choose_succ_succ, choose_val_22_15, choose_val_22_16]
theorem choose_val_23_17 : Nat.choose 23 17 = 100947 := by
  rw [Nat.choose_succ_succ, choose_val_22_16, choose_val_22_17]
theorem choose_val_23_18 : Nat.choose 23 18 = 33649 := by
  rw [Nat.choose_succ_succ, choose_val_22_17, choose_val_22_18]
theorem choose_val_23_19 : Nat.choose 23 19 = 8855 := by
  rw [Nat.choose_succ_succ, choose_val_22_18, choose_val_22_19]
theorem choose_val_23_20 : Nat.choose 23 20 = 1771 := by
  rw [Nat.choose_succ_succ, choose_val_22_19, choose_val_22_20]
theorem choose_val_23_21 : Nat.choose 23 21 = 253 := by
  rw [Nat.choose_succ_succ, choose_val_22_20, choose_val_22_21]
theorem choose_val_23_22 : Nat.choose 23 22 = 23 := by
  rw [Nat.choose_succ_succ, choose_val_22_21, choose_val_22_22]
theorem choose_val_23_23 : Nat.choose 23 23 = 1 := Nat.choose_self _
theorem choose_val_24_0 : Nat.choose 24 0 = 1 := Nat.choose_zero_right _
theorem choose_val_24_1 : Nat.choose 24 1 = 24 := Nat.choose_one_right _
theorem choose_val_24_2 : Nat.choose 24 2 = 276 := by
  rw [Nat.choose_succ_succ, choose_val_23_1, choose_val_23_2]
theorem choose_val_24_3 : Nat.choose 24 3 = 2024 := by
  rw [Nat.choose_succ_succ, choose_val_23_2, choose_val_23_3]
theorem choose_val_24_4 : Nat.choose 24 4 = 10626 := by
  rw [Nat.choose_succ_succ, choose_val_23_3, choose_val_23_4]
theorem choose_val_24_5 : Nat.choose 24 5 = 42504 := by
  rw [Nat.choose_succ_succ, choose_val_23_4, choose_val_23_5]
theorem choose_val_24_6 : Nat.choose 24 6 = 134596 := by
  rw [Nat.choose_succ_succ, choose_val_23_5, choose_val_23_6]
theorem choose_val_24_7 : Nat.choose 24 7 = 346104 := by
  rw [Nat.choose_succ_succ, choose_val_23_6, choose_val_23_7]
theorem choose_val_24_8 : Nat.choose 24 8 = 735471 := by
  rw [Nat.choose_succ_succ, choose_val_23_7, choose_val_23_8]
theorem choose_val_24_9 : Nat.choose 24 9 = 1307504 := by
  rw [Nat.choose_succ_succ, choose_val_23_8, choose_val_23_9]
theorem choose_val_24_10 : Nat.choose 24 10 = 1961256 := by
  rw [Nat.choose_succ_succ, choose_val_23_9, choose_val_23_10]
theorem choose_val_24_11 : Nat.choose 24 11 = 2496144 := by
  rw [Nat.choose_succ_succ, choose_val_23_10, choose_val_23_11]
theorem choose_val_24_12 : Nat.choose 24 12 = 2704156 := by
  rw [Nat.choose_succ_succ, choose_val_23_11, choose_val_23_12]
theorem choose_val_24_13 : Nat.choose 24 13 = 2496144 := by
  rw [Nat.choose_succ_succ, choose_val_23_12, choose_val_23_13]
theorem choose_val_24_14 : Nat.choose 24 14 = 1961256 := by
  rw [Nat.choose_succ_succ, choose_val_23_13, choose_val_23_14]
theorem choose_val_24_15 : Nat.choose 24 15 = 1307504 := by
  rw [Nat.choose_succ_succ, choose_val_23_14, choose_val_23_15]
theorem choose_val_24_16 : Nat.choose 24 16 = 735471 := by
  rw [Nat.choose_succ_succ, choose_val_23_15, choose_val_23_16]
theorem choose_val_24_17 : Nat.choose 24 17 = 346104 := by
  rw [Nat.choose_succ_succ, choose_val_23_16, choose_val_23_17]
theorem choose_val_24_18 : Nat.choose 24 18 = 134596 := by
  rw [Nat.choose_succ_succ, choose_val_23_17, choose_val_23_18]
theorem choose_val_24_19 : Nat.choose 24 19 = 42504 := by
  rw [Nat.choose_succ_succ, choose_val_23_18, choose_val_23_19]
theorem choose_val_24_20 : Nat.choose 24 20 = 10626 := by
  rw [Nat.choose_succ_succ, choose_val_23_19, choose_val_23_20]
theorem choose_val_24_21 : Nat.choose 24 21 = 2024 := by
  rw [Nat.choose_succ_succ, choose_val_23_20, choose_val_23_21]
theorem choose_val_24_22 : Nat.choose 24 22 = 276 := by
  rw [Nat.choose_succ_succ, choose_val_23_21, choose_val_23_22]
theorem choose_val_24_23 : Nat.choose 24 23 = 24 := by
  rw [Nat.choose_succ_succ, choose_val_23_22, choose_val_23_23]
theorem choose_val_24_24 : Nat.choose 24 24 = 1 := Nat.choose_self _
theorem choose_val_25_0 : Nat.choose 25 0 = 1 := Nat.choose_zero_right _
theorem choose_val_25_1 : Nat.choose 25 1 = 25 := Nat.choose_one_right _
theorem choose_val_25_2 : Nat.choose 25 2 = 300 := by
  rw [Nat.choose_succ_succ, choose_val_24_1, choose_val_24_2]
theorem choose_val_25_3 : Nat.choose 25 3 = 2300 := by
  rw [Nat.choose_succ_succ, choose_val_24_2, choose_val_24_3]
theorem choose_val_25_4 : Nat.choose 25 4 = 12650 := by
  rw [Nat.choose_succ_succ, choose_val_24_3, choose_val_24_4]
theorem choose_val_25_5 : Nat.choose 25 5 = 53130 := by
  rw [Nat.choose_succ_succ, choose_val_24_4, choose_val_24_5]
theorem choose_val_25_6 : Nat.choose 25 6 = 177100 := by
  rw [Nat.choose_succ_succ, choose_val_24_5, choose_val_24_6]
theorem choose_val_25_7 : Nat.choose 25 7 = 480700 := by
  rw [Nat.choose_succ_succ, choose_val_24_6, choose_val_24_7]
theorem choose_val_25_8 : Nat.choose 25 8 = 1081575 := by
  rw [Nat.choose_succ_succ, choose_val_24_7, choose_val_24_8]
theorem choose_val_25_9 : Nat.choose 25 9 = 2042975 := by
  rw [Nat.choose_succ_succ, choose_val_24_8, choose_val_24_9]
theorem choose_val_25_10 : Nat.choose 25 10 = 3268760 := by
  rw [Nat.choose_succ_succ, choose_val_24_9, choose_val_24_10]
theorem choose_val_25_11 : Nat.choose 25 11 = 4457400 := by
  rw [Nat.choose_succ_succ, choose_val_24_10, choose_val_24_11]
theorem choose_val_25_12 : Nat.choose 25 12 = 5200300 := by
  rw [Nat.choose_succ_succ, choose_val_24_11, choose_val_24_12]
theorem choose_val_25_13 : Nat.choose 25 13 = 5200300 := by
  rw [Nat.choose_succ_succ, choose_val_24_12, choose_val_24_13]
theorem choose_val_25_14 : Nat.choose 25 14 = 4457400 := by
  rw [Nat.choose_succ_succ, choose_val_24_13, choose_val_24_14]
theorem choose_val_25_15 : Nat.choose 25 15 = 3268760 := by
  rw [Nat.choose_succ_succ, choose_val_24_14, choose_val_24_15]
theorem choose_val_25_16 : Nat.choose 25 16 = 2042975 := by
  rw [Nat.choose_succ_succ, choose_val_24_15, choose_val_24_16]
theorem choose_val_25_17 : Nat.choose 25 17 = 1081575 := by
  rw [Nat.choose_succ_succ, choose_val_24_16, choose_val_24_17]
theorem choose_val_25_18 : Nat.choose 25 18 = 480700 := by
  rw [Nat.choose_succ_succ, choose_val_24_17, choose_val_24_18]
theorem choose_val_25_19 : Nat.choose 25 19 = 177100 := by
  rw [Nat.choose_succ_succ, choose_val_24_18, choose_val_24_19]
theorem choose_val_25_20 : Nat.choose 25 20 = 53130 := by
  rw [Nat.choose_succ_succ, choose_val_24_19, choose_val_24_20]
theorem choose_val_25_21 : Nat.choose 25 21 = 12650 := by
  rw [Nat.choose_succ_succ, choose_val_24_20, choose_val_24_21]
theorem choose_val_25_22 : Nat.choose 25 22 = 2300 := by
  rw [Nat.choose_succ_succ, choose_val_24_21, choose_val_24_22]
theorem choose_val_25_23 : Nat.choose 25 23 = 300 := by
  rw [Nat.choose_succ_succ, choose_val_24_22, choose_val_24_23]
theorem choose_val_25_24 : Nat.choose 25 24 = 25 := by
  rw [Nat.choose_succ_succ, choose_val_24_23, choose_val_24_24]
theorem choose_val_25_25 : Nat.choose 25 25 = 1 := Nat.choose_self _
theorem choose_val_26_0 : Nat.choose 26 0 = 1 := Nat.choose_zero_right _
theorem choose_val_26_1 : Nat.choose 26 1 = 26 := Nat.choose_one_right _
theorem choose_val_26_2 : Nat.choose 26 2 = 325 := by
  rw [Nat.choose_succ_succ, choose_val_25_1, choose_val_25_2]
theorem choose_val_26_3 : Nat.choose 26 3 = 2600 := by
  rw [Nat.choose_succ_succ, choose_val_25_2, choose_val_25_3]
theorem choose_val_26_4 : Nat.choose 26 4 = 14950 := by
  rw [Nat.choose_succ_succ, choose_val_25_3, choose_val_25_4]
theorem choose_val_26_5 : Nat.choose 26 5 = 65780 := by
  rw [Nat.choose_succ_succ, choose_val_25_4, choose_val_25_5]
theorem choose_val_26_6 : Nat.choose 26 6 = 230230 := by
  rw [Nat.choose_succ_succ, choose_val_25_5, choose_val_25_6]
theorem choose_val_26_7 : Nat.choose 26 7 = 657800 := by
  rw [Nat.choose_succ_succ, choose_val_25_6, choose_val_25_7]
theorem choose_val_26_8 : Nat.choose 26 8 = 1562275 := by
  rw [Nat.choose_succ_succ, choose_val_25_7, choose_val_25_8]
theorem choose_val_26_9 : Nat.choose 26 9 = 3124550 := by
  rw [Nat.choose_succ_succ, choose_val_25_8, choose_val_25_9]
theorem choose_val_26_10 : Nat.choose 26 10 = 5311735 := by
  rw [Nat.choose_succ_succ, choose_val_25_9, choose_val_25_10]
theorem choose_val_26_11 : Nat.choose 26 11 = 7726160 := by
  rw [Nat.choose_succ_succ, choose_val_25_10, choose_val_25_11]
theorem choose_val_26_12 : Nat.choose 26 12 = 9657700 := by
  rw [Nat.choose_succ_succ, choose_val_25_11, choose_val_25_12]
theorem choose_val_26_13 : Nat.choose 26 13 = 10400600 := by
  rw [Nat.choose_succ_succ, choose_val_25_12, choose_val_25_13]
theorem choose_val_26_14 : Nat.choose 26 14 = 9657700 := by
  rw [Nat.choose_succ_succ, choose_val_25_13, choose_val_25_14]
theorem choose_val_26_15 : Nat.choose 26 15 = 7726160 := by
  rw [Nat.choose_succ_succ, choose_val_25_14, choose_val_25_15]
theorem choose_val_26_16 : Nat.choose 26 16 = 5311735 := by
  rw [Nat.choose_succ_succ, choose_val_25_15, choose_val_25_16]
theorem choose_val_26_17 : Nat.choose 26 17 = 3124550 := by
  rw [Nat.choose_succ_succ, choose_val_25_16, choose_val_25_17]
theorem choose_val_26_18 : Nat.choose 26 18 = 1562275 := by
  rw [Nat.choose_succ_succ, choose_val_25_17, choose_val_25_18]
theorem choose_val_26_19 : Nat.choose 26 19 = 657800 := by
  rw [Nat.choose_succ_succ, choose_val_25_18, choose_val_25_19]
theorem choose_val_26_20 : Nat.choose 26 20 = 230230 := by
  rw [Nat.choose_succ_succ, choose_val_25_19, choose_val_25_20]
theorem choose_val_26_21 : Nat.choose 26 21 = 65780 := by
  rw [Nat.choose_succ_succ, choose_val_25_20, choose_val_25_21]
theorem choose_val_26_22 : Nat.choose 26 22 = 14950 := by
  rw [Nat.choose_succ_succ, choose_val_25_21, choose_val_25_22]
theorem choose_val_26_23 : Nat.choose 26 23 = 2600 := by
  rw [Nat.choose_succ_succ, choose_val_25_22, choose_val_25_23]
theorem choose_val_26_24 : Nat.choose 26 24 = 325 := by
  rw [Nat.choose_succ_succ, choose_val_25_23, choose_val_25_24]
theorem choose_val_26_25 : Nat.choose 26 25 = 26 := by
  rw [Nat.choose_succ_succ, choose_val_25_24, choose_val_25_25]
theorem choose_val_26_26 : Nat.choose 26 26 = 1 := Nat.choose_self _
theorem choose_val_27_0 : Nat.choose 27 0 = 1 := Nat.choose_zero_right _
theorem choose_val_27_1 : Nat.choose 27 1 = 27 := Nat.choose_one_right _
theorem choose_val_27_2 : Nat.choose 27 2 = 351 := by
  rw [Nat.choose_succ_succ, choose_val_26_1, choose_val_26_2]
theorem choose_val_27_3 : Nat.choose 27 3 = 2925 := by
  rw [Nat.choose_succ_succ, choose_val_26_2, choose_val_26_3]
theorem choose_val_27_4 : Nat.choose 27 4 = 17550 := by
  rw [Nat.choose_succ_succ, choose_val_26_3, choose_val_26_4]
theorem choose_val_27_5 : Nat.choose 27 5 = 80730 := by
  rw [Nat.choose_succ_succ, choose_val_26_4, choose_val_26_5]
theorem choose_val_27_6 : Nat.choose 27 6 = 296010 := by
  rw [Nat.choose_succ_succ, choose_val_26_5, choose_val_26_6]
theorem choose_val_27_7 : Nat.choose 27 7 = 888030 := by
  rw [Nat.choose_succ_succ, choose_val_26_6, choose_val_26_7]
theorem choose_val_27_8 : Nat.choose 27 8 = 2220075 := by
  rw [Nat.choose_succ_succ, choose_val_26_7, choose_val_26_8]
theorem choose_val_27_9 : Nat.choose 27 9 = 4686825 := by
  rw [Nat.choose_succ_succ, choose_val_26_8, choose_val_26_9]
theorem choose_val_27_10 : Nat.choose 27 10 = 8436285 := by
  rw [Nat.choose_succ_succ, choose_val_26_9, choose_val_26_10]
theorem choose_val_27_11 : Nat.choose 27 11 = 13037895 := by
  rw [Nat.choose_succ_succ, choose_val_26_10, choose_val_26_11]
theorem choose_val_27_12 : Nat.choose 27 12 = 17383860 := by
  rw [Nat.choose_succ_succ, choose_val_26_11, choose_val_26_12]
theorem choose_val_27_13 : Nat.choose 27 13 = 20058300 := by
  rw [Nat.choose_succ_succ, choose_val_26_12, choose_val_26_13]
theorem choose_val_27_14 : Nat.choose 27 14 = 20058300 := by
  rw [Nat.choose_succ_succ, choose_val_26_13, choose_val_26_14]
theorem choose_val_27_15 : Nat.choose 27 15 = 17383860 := by
  rw [Nat.choose_succ_succ, choose_val_26_14, choose_val_26_15]
theorem choose_val_27_16 : Nat.choose 27 16 = 13037895 := by
  rw [Nat.choose_succ_succ, choose_val_26_15, choose_val_26_16]
theorem choose_val_27_17 : Nat.choose 27 17 = 8436285 := by
  rw [Nat.choose_succ_succ, choose_val_26_16, choose_val_26_17]
theorem choose_val_27_18 : Nat.choose 27 18 = 4686825 := by
  rw [Nat.choose_succ_succ, choose_val_26_17, choose_val_26_18]
theorem choose_val_27_19 : Nat.choose 27 19 = 2220075 := by
  rw [Nat.choose_succ_succ, choose_val_26_18, choose_val_26_19]
theorem choose_val_27_20 : Nat.choose 27 20 = 888030 := by
  rw [Nat.choose_succ_succ, choose_val_26_19, choose_val_26_20]
theorem choose_val_27_21 : Nat.choose 27 21 = 296010 := by
  rw [Nat.choose_succ_succ, choose_val_26_20, choose_val_26_21]
theorem choose_val_27_22 : Nat.choose 27 22 = 80730 := by
  rw [Nat.choose_succ_succ, choose_val_26_21, choose_val_26_22]
theorem choose_val_27_23 : Nat.choose 27 23 = 17550 := by
  rw [Nat.choose_succ_succ, choose_val_26_22, choose_val_26_23]
theorem choose_val_27_24 : Nat.choose 27 24 = 2925 := by
  rw [Nat.choose_succ_succ, choose_val_26_23, choose_val_26_24]
theorem choose_val_27_25 : Nat.choose 27 25 = 351 := by
  rw [Nat.choose_succ_succ, choose_val_26_24, choose_val_26_25]
theorem choose_val_27_26 : Nat.choose 27 26 = 27 := by
  rw [Nat.choose_succ_succ, choose_val_26_25, choose_val_26_26]
theorem choose_val_27_27 : Nat.choose 27 27 = 1 := Nat.choose_self _
theorem choose_val_28_0 : Nat.choose 28 0 = 1 := Nat.choose_zero_right _
theorem choose_val_28_1 : Nat.choose 28 1 = 28 := Nat.choose_one_right _
theorem choose_val_28_2 : Nat.choose 28 2 = 378 := by
  rw [Nat.choose_succ_succ, choose_val_27_1, choose_val_27_2]
theorem choose_val_28_3 : Nat.choose 28 3 = 3276 := by
  rw [Nat.choose_succ_succ, choose_val_27_2, choose_val_27_3]
theorem choose_val_28_4 : Nat.choose 28 4 = 20475 := by
  rw [Nat.choose_succ_succ, choose_val_27_3, choose_val_27_4]
theorem choose_val_28_5 : Nat.choose 28 5 = 98280 := by
  rw [Nat.choose_succ_succ, choose_val_27_4, choose_val_27_5]
theorem choose_val_28_6 : Nat.choose 28 6 = 376740 := by
  rw [Nat.choose_succ_succ, choose_val_27_5, choose_val_27_6]
theorem choose_val_28_7 : Nat.choose 28 7 = 1184040 := by
  rw [Nat.choose_succ_succ, choose_val_27_6, choose_val_27_7]
theorem choose_val_28_8 : Nat.choose 28 8 = 3108105 := by
  rw [Nat.choose_succ_succ, choose_val_27_7, choose_val_27_8]
theorem choose_val_28_9 : Nat.choose 28 9 = 6906900 := by
  rw [Nat.choose_succ_succ, choose_val_27_8, choose_val_27_9]
theorem choose_val_28_10 : Nat.choose 28 10 = 13123110 := by
  rw [Nat.choose_succ_succ, choose_val_27_9, choose_val_27_10]
theorem choose_val_28_11 : Nat.choose 28 11 = 21474180 := by
  rw [Nat.choose_succ_succ, choose_val_27_10, choose_val_27_11]
theorem choose_val_28_12 : Nat.choose 28 12 = 30421755 := by
  rw [Nat.choose_succ_succ, choose_val_27_11, choose_val_27_12]
theorem choose_val_28_13 : Nat.choose 28 13 = 37442160 := by
  rw [Nat.choose_succ_succ, choose_val_27_12, choose_val_27_13]
theorem choose_val_28_14 : Nat.choose 28 14 = 40116600 := by
  rw [Nat.choose_succ_succ, choose_val_27_13, choose_val_27_14]
theorem choose_val_28_15 : Nat.choose 28 15 = 37442160 := by
  rw [Nat.choose_succ_succ, choose_val_27_14, choose_val_27_15]
theorem choose_val_28_16 : Nat.choose 28 16 = 30421755 := by
  rw [Nat.choose_succ_succ, choose_val_27_15, choose_val_27_16]
theorem choose_val_28_17 : Nat.choose 28 17 = 21474180 := by
  rw [Nat.choose_succ_succ, choose_val_27_16, choose_val_27_17]
theorem choose_val_28_18 : Nat.choose 28 18 = 13123110 := by
  rw [Nat.choose_succ_succ, choose_val_27_17, choose_val_27_18]
theorem choose_val_28_19 : Nat.choose 28 19 = 6906900 := by
  rw [Nat.choose_succ_succ, choose_val_27_18, choose_val_27_19]
theorem choose_val_28_20 : Nat.choose 28 20 = 3108105 := by
  rw [Nat.choose_succ_succ, choose_val_27_19, choose_val_27_20]
theorem choose_val_28_21 : Nat.choose 28 21 = 1184040 := by
  rw [Nat.choose_succ_succ, choose_val_27_20, choose_val_27_21]
theorem choose_val_28_22 : Nat.choose 28 22 = 376740 := by
  rw [Nat.choose_succ_succ, choose_val_27_21, choose_val_27_22]
theorem choose_val_28_23 : Nat.choose 28 23 = 98280 := by
  rw [Nat.choose_succ_succ, choose_val_27_22, choose_val_27_23]
theorem choose_val_28_24 : Nat.choose 28 24 = 20475 := by
  rw [Nat.choose_succ_succ, choose_val_27_23, choose_val_27_24]
theorem choose_val_28_25 : Nat.choose 28 25 = 3276 := by
  rw [Nat.choose_succ_succ, choose_val_27_24, choose_val_27_25]
theorem choose_val_28_26 : Nat.choose 28 26 = 378 := by
  rw [Nat.choose_succ_succ, choose_val_27_25, choose_val_27_26]
theorem choose_val_28_27 : Nat.choose 28 27 = 28 := by
  rw [Nat.choose_succ_succ, choose_val_27_26, choose_val_27_27]
theorem choose_val_28_28 : Nat.choose 28 28 = 1 := Nat.choose_self _
theorem choose_val_29_0 : Nat.choose 29 0 = 1 := Nat.choose_zero_right _
theorem choose_val_29_1 : Nat.choose 29 1 = 29 := Nat.choose_one_right _
theorem choose_val_29_2 : Nat.choose 29 2 = 406 := by
  rw [Nat.choose_succ_succ, choose_val_28_1, choose_val_28_2]
theorem choose_val_29_3 : Nat.choose 29 3 = 3654 := by
  rw [Nat.choose_succ_succ, choose_val_28_2, choose_val_28_3]
theorem choose_val_29_4 : Nat.choose 29 4 = 23751 := by
  rw [Nat.choose_succ_succ, choose_val_28_3, choose_val_28_4]
theorem choose_val_29_5 : Nat.choose 29 5 = 118755 := by
  rw [Nat.choose_succ_succ, choose_val_28_4, choose_val_28_5]
theorem choose_val_29_6 : Nat.choose 29 6 = 475020 := by
  rw [Nat.choose_succ_succ, choose_val_28_5, choose_val_28_6]
theorem choose_val_29_7 : Nat.choose 29 7 = 1560780 := by
  rw [Nat.choose_succ_succ, choose_val_28_6, choose_val_28_7]
theorem choose_val_29_8 : Nat.choose 29 8 = 4292145 := by
  rw [Nat.choose_succ_succ, choose_val_28_7, choose_val_28_8]
theorem choose_val_29_9 : Nat.choose 29 9 = 10015005 := by
  rw [Nat.choose_succ_succ, choose_val_28_8, choose_val_28_9]
theorem choose_val_29_10 : Nat.choose 29 10 = 20030010 := by
  rw [Nat.choose_succ_succ, choose_val_28_9, choose_val_28_10]
theorem choose_val_29_11 : Nat.choose 29 11 = 34597290 := by
  rw [Nat.choose_succ_succ, choose_val_28_10, choose_val_28_11]
theorem choose_val_29_12 : Nat.choose 29 12 = 51895935 := by
  rw [Nat.choose_succ_succ, choose_val_28_11, choose_val_28_12]
theorem choose_val_29_13 : Nat.choose 29 13 = 67863915 := by
  rw [Nat.choose_succ_succ, choose_val_28_12, choose_val_28_13]
theorem choose_val_29_14 : Nat.choose 29 14 = 77558760 := by
  rw [Nat.choose_succ_succ, choose_val_28_13, choose_val_28_14]
theorem choose_val_29_15 : Nat.choose 29 15 = 77558760 := by
  rw [Nat.choose_succ_succ, choose_val_28_14, choose_val_28_15]
theorem choose_val_29_16 : Nat.choose 29 16 = 67863915 := by
  rw [Nat.choose_succ_succ, choose_val_28_15, choose_val_28_16]
theorem choose_val_29_17 : Nat.choose 29 17 = 51895935 := by
  rw [Nat.choose_succ_succ, choose_val_28_16, choose_val_28_17]
theorem choose_val_29_18 : Nat.choose 29 18 = 34597290 := by
  rw [Nat.choose_succ_succ, choose_val_28_17, choose_val_28_18]
theorem choose_val_29_19 : Nat.choose 29 19 = 20030010 := by
  rw [Nat.choose_succ_succ, choose_val_28_18, choose_val_28_19]
theorem choose_val_29_20 : Nat.choose 29 20 = 10015005 := by
  rw [Nat.choose_succ_succ, choose_val_28_19, choose_val_28_20]
theorem choose_val_29_21 : Nat.choose 29 21 = 4292145 := by
  rw [Nat.choose_succ_succ, choose_val_28_20, choose_val_28_21]
theorem choose_val_29_22 : Nat.choose 29 22 = 1560780 := by
  rw [Nat.choose_succ_succ, choose_val_28_21, choose_val_28_22]
theorem choose_val_29_23 : Nat.choose 29 23 = 475020 := by
  rw [Nat.choose_succ_succ, choose_val_28_22, choose_val_28_23]
theorem choose_val_29_24 : Nat.choose 29 24 = 118755 := by
  rw [Nat.choose_succ_succ, choose_val_28_23, choose_val_28_24]
theorem choose_val_29_25 : Nat.choose 29 25 = 23751 := by
  rw [Nat.choose_succ_succ, choose_val_28_24, choose_val_28_25]
theorem choose_val_29_26 : Nat.choose 29 26 = 3654 := by
  rw [Nat.choose_succ_succ, choose_val_28_25, choose_val_28_26]
theorem choose_val_29_27 : Nat.choose 29 27 = 406 := by
  rw [Nat.choose_succ_succ, choose_val_28_26, choose_val_28_27]
theorem choose_val_29_28 : Nat.choose 29 28 = 29 := by
  rw [Nat.choose_succ_succ, choose_val_28_27, choose_val_28_28]
theorem choose_val_29_29 : Nat.choose 29 29 = 1 := Nat.choose_self _
theorem choose_val_30_0 : Nat.choose 30 0 = 1 := Nat.choose_zero_right _
theorem choose_val_30_1 : Nat.choose 30 1 = 30 := Nat.choose_one_right _
theorem choose_val_30_2 : Nat.choose 30 2 = 435 := by
  rw [Nat.choose_succ_succ, choose_val_29_1, choose_val_29_2]
theorem choose_val_30_3 : Nat.choose 30 3 = 4060 := by
  rw [Nat.choose_succ_succ, choose_val_29_2, choose_val_29_3]
theorem choose_val_30_4 : Nat.choose 30 4 = 27405 := by
  rw [Nat.choose_succ_succ, choose_val_29_3, choose_val_29_4]
theorem choose_val_30_5 : Nat.choose 30 5 = 142506 := by
  rw [Nat.choose_succ_succ, choose_val_29_4, choose_val_29_5]
theorem choose_val_30_6 : Nat.choose 30 6 = 593775 := by
  rw [Nat.choose_succ_succ, choose_val_29_5, choose_val_29_6]
theorem choose_val_30_7 : Nat.choose 30 7 = 2035800 := by
  rw [Nat.choose_succ_succ, choose_val_29_6, choose_val_29_7]
theorem choose_val_30_8 : Nat.choose 30 8 = 5852925 := by
  rw [Nat.choose_succ_succ, choose_val_29_7, choose_val_29_8]
theorem choose_val_30_9 : Nat.choose 30 9 = 14307150 := by
  rw [Nat.choose_succ_succ, choose_val_29_8, choose_val_29_9]
theorem choose_val_30_10 : Nat.choose 30 10 = 30045015 := by
  rw [Nat.choose_succ_succ, choose_val_29_9, choose_val_29_10]
theorem choose_val_30_11 : Nat.choose 30 11 = 54627300 := by
  rw [Nat.choose_succ_succ, choose_val_29_10, choose_val_29_11]
theorem choose_val_30_12 : Nat.choose 30 12 = 86493225 := by
  rw [Nat.choose_succ_succ, choose_val_29_11, choose_val_29_12]
theorem choose_val_30_13 : Nat.choose 30 13 = 119759850 := by
  rw [Nat.choose_succ_succ, choose_val_29_12, choose_val_29_13]
theorem choose_val_30_14 : Nat.choose 30 14 = 145422675 := by
  rw [Nat.choose_succ_succ, choose_val_29_13, choose_val_29_14]
theorem choose_val_30_15 : Nat.choose 30 15 = 155117520 := by
  rw [Nat.choose_succ_succ, choose_val_29_14, choose_val_29_15]
theorem choose_val_30_16 : Nat.choose 30 16 = 145422675 := by
  rw [Nat.choose_succ_succ, choose_val_29_15, choose_val_29_16]
theorem choose_val_30_17 : Nat.choose 30 17 = 119759850 := by
  rw [Nat.choose_succ_succ, choose_val_29_16, choose_val_29_17]
theorem choose_val_30_18 : Nat.choose 30 18 = 86493225 := by
  rw [Nat.choose_succ_succ, choose_val_29_17, choose_val_29_18]
theorem choose_val_30_19 : Nat.choose 30 19 = 54627300 := by
  rw [Nat.choose_succ_succ, choose_val_29_18, choose_val_29_19]
theorem choose_val_30_20 : Nat.choose 30 20 = 30045015 := by
  rw [Nat.choose_succ_succ, choose_val_29_19, choose_val_29_20]
theorem choose_val_30_21 : Nat.choose 30 21 = 14307150 := by
  rw [Nat.choose_succ_succ, choose_val_29_20, choose_val_29_21]
theorem choose_val_30_22 : Nat.choose 30 22 = 5852925 := by
  rw [Nat.choose_succ_succ, choose_val_29_21, choose_val_29_22]
theorem choose_val_30_23 : Nat.choose 30 23 = 2035800 := by
  rw [Nat.choose_succ_succ, choose_val_29_22, choose_val_29_23]
theorem choose_val_30_24 : Nat.choose 30 24 = 593775 := by
  rw [Nat.choose_succ_succ, choose_val_29_23, choose_val_29_24]
theorem choose_val_30_25 : Nat.choose 30 25 = 142506 := by
  rw [Nat.choose_succ_succ, choose_val_29_24, choose_val_29_25]
theorem choose_val_30_26 : Nat.choose 30 26 = 27405 := by
  rw [Nat.choose_succ_succ, choose_val_29_25, choose_val_29_26]
theorem choose_val_30_27 : Nat.choose 30 27 = 4060 := by
  rw [Nat.choose_succ_succ, choose_val_29_26, choose_val_29_27]
theorem choose_val_30_28 : Nat.choose 30 28 = 435 := by
  rw [Nat.choose_succ_succ, choose_val_29_27, choose_val_29_28]
theorem choose_val_30_29 : Nat.choose 30 29 = 30 := by
  rw [Nat.choose_succ_succ, choose_val_29_28, choose_val_29_29]
theorem choose_val_30_30 : Nat.choose 30 30 = 1 := Nat.choose_self _
theorem choose_val_31_0 : Nat.choose 31 0 = 1 := Nat.choose_zero_right _
theorem choose_val_31_1 : Nat.choose 31 1 = 31 := Nat.choose_one_right _
theorem choose_val_31_2 : Nat.choose 31 2 = 465 := by
  rw [Nat.choose_succ_succ, choose_val_30_1, choose_val_30_2]
theorem choose_val_31_3 : Nat.choose 31 3 = 4495 := by
  rw [Nat.choose_succ_succ, choose_val_30_2, choose_val_30_3]
theorem choose_val_31_4 : Nat.choose 31 4 = 31465 := by
  rw [Nat.choose_succ_succ, choose_val_30_3, choose_val_30_4]
theorem choose_val_31_5 : Nat.choose 31 5 = 169911 := by
  rw [Nat.choose_succ_succ, choose_val_30_4, choose_val_30_5]
theorem choose_val_31_6 : Nat.choose 31 6 = 736281 := by
  rw [Nat.choose_succ_succ, choose_val_30_5, choose_val_30_6]
theorem choose_val_31_7 : Nat.choose 31 7 = 2629575 := by
  rw [Nat.choose_succ_succ, choose_val_30_6, choose_val_30_7]
theorem choose_val_31_8 : Nat.choose 31 8 = 7888725 := by
  rw [Nat.choose_succ_succ, choose_val_30_7, choose_val_30_8]
theorem choose_val_31_9 : Nat.choose 31 9 = 20160075 := by
  rw [Nat.choose_succ_succ, choose_val_30_8, choose_val_30_9]
theorem choose_val_31_10 : Nat.choose 31 10 = 44352165 := by
  rw [Nat.choose_succ_succ, choose_val_30_9, choose_val_30_10]
theorem choose_val_31_11 : Nat.choose 31 11 = 84672315 := by
  rw [Nat.choose_succ_succ, choose_val_30_10, choose_val_30_11]
theorem choose_val_31_12 : Nat.choose 31 12 = 141120525 := by
  rw [Nat.choose_succ_succ, choose_val_30_11, choose_val_30_12]
theorem choose_val_31_13 : Nat.choose 31 13 = 206253075 := by
  rw [Nat.choose_succ_succ, choose_val_30_12, choose_val_30_13]
theorem choose_val_31_14 : Nat.choose 31 14 = 265182525 := by
  rw [Nat.choose_succ_succ, choose_val_30_13, choose_val_30_14]
theorem choose_val_31_15 : Nat.choose 31 15 = 300540195 := by
  rw [Nat.choose_succ_succ, choose_val_30_14, choose_val_30_15]
theorem choose_val_31_16 : Nat.choose 31 16 = 300540195 := by
  rw [Nat.choose_succ_succ, choose_val_30_15, choose_val_30_16]
theorem choose_val_31_17 : Nat.choose 31 17 = 265182525 := by
  rw [Nat.choose_succ_succ, choose_val_30_16, choose_val_30_17]
theorem choose_val_31_18 : Nat.choose 31 18 = 206253075 := by
  rw [Nat.choose_succ_succ, choose_val_30_17, choose_val_30_18]
theorem choose_val_31_19 : Nat.choose 31 19 = 141120525 := by
  rw [Nat.choose_succ_succ, choose_val_30_18, choose_val_30_19]
theorem choose_val_31_20 : Nat.choose 31 20 = 84672315 := by
  rw [Nat.choose_succ_succ, choose_val_30_19, choose_val_30_20]
theorem choose_val_31_21 : Nat.choose 31 21 = 44352165 := by
  rw [Nat.choose_succ_succ, choose_val_30_20, choose_val_30_21]
theorem choose_val_31_22 : Nat.choose 31 22 = 20160075 := by
  rw [Nat.choose_succ_succ, choose_val_30_21, choose_val_30_22]
theorem choose_val_31_23 : Nat.choose 31 23 = 7888725 := by
  rw [Nat.choose_succ_succ, choose_val_30_22, choose_val_30_23]
theorem choose_val_31_24 : Nat.choose 31 24 = 2629575 := by
  rw [Nat.choose_succ_succ, choose_val_30_23, choose_val_30_24]
theorem choose_val_31_25 : Nat.choose 31 25 = 736281 := by
  rw [Nat.choose_succ_succ, choose_val_30_24, choose_val_30_25]
theorem choose_val_31_26 : Nat.choose 31 26 = 169911 := by
  rw [Nat.choose_succ_succ, choose_val_30_25, choose_val_30_26]
theorem choose_val_31_27 : Nat.choose 31 27 = 31465 := by
  rw [Nat.choose_succ_succ, choose_val_30_26, choose_val_30_27]
theorem choose_val_31_28 : Nat.choose 31 28 = 4495 := by
  rw [Nat.choose_succ_succ, choose_val_30_27, choose_val_30_28]
theorem choose_val_31_29 : Nat.choose 31 29 = 465 := by
  rw [Nat.choose_succ_succ, choose_val_30_28, choose_val_30_29]
theorem choose_val_31_30 : Nat.choose 31 30 = 31 := by
  rw [Nat.choose_succ_succ, choose_val_30_29, choose_val_30_30]
theorem choose_val_31_31 : Nat.choose 31 31 = 1 := Nat.choose_self _
theorem choose_val_32_0 : Nat.choose 32 0 = 1 := Nat.choose_zero_right _
theorem choose_val_32_1 : Nat.choose 32 1 = 32 := Nat.choose_one_right _
theorem choose_val_32_2 : Nat.choose 32 2 = 496 := by
  rw [Nat.choose_succ_succ, choose_val_31_1, choose_val_31_2]
theorem choose_val_32_3 : Nat.choose 32 3 = 4960 := by
  rw [Nat.choose_succ_succ, choose_val_31_2, choose_val_31_3]
theorem choose_val_32_4 : Nat.choose 32 4 = 35960 := by
  rw [Nat.choose_succ_succ, choose_val_31_3, choose_val_31_4]
theorem choose_val_32_5 : Nat.choose 32 5 = 201376 := by
  rw [Nat.choose_succ_succ, choose_val_31_4, choose_val_31_5]
theorem choose_val_32_6 : Nat.choose 32 6 = 906192 := by
  rw [Nat.choose_succ_succ, choose_val_31_5, choose_val_31_6]
theorem choose_val_32_7 : Nat.choose 32 7 = 3365856 := by
  rw [Nat.choose_succ_succ, choose_val_31_6, choose_val_31_7]
theorem choose_val_32_8 : Nat.choose 32 8 = 10518300 := by
  rw [Nat.choose_succ_succ, choose_val_31_7, choose_val_31_8]
theorem choose_val_32_9 : Nat.choose 32 9 = 28048800 := by
  rw [Nat.choose_succ_succ, choose_val_31_8, choose_val_31_9]
theorem choose_val_32_10 : Nat.choose 32 10 = 64512240 := by
  rw [Nat.choose_succ_succ, choose_val_31_9, choose_val_31_10]
theorem choose_val_32_11 : Nat.choose 32 11 = 129024480 := by
  rw [Nat.choose_succ_succ, choose_val_31_10, choose_val_31_11]
theorem choose_val_32_12 : Nat.choose 32 12 = 225792840 := by
  rw [Nat.choose_succ_succ, choose_val_31_11, choose_val_31_12]
theorem choose_val_32_13 : Nat.choose 32 13 = 347373600 := by
  rw [Nat.choose_succ_succ, choose_val_31_12, choose_val_31_13]
theorem choose_val_32_14 : Nat.choose 32 14 = 471435600 := by
  rw [Nat.choose_succ_succ, choose_val_31_13, choose_val_31_14]
theorem choose_val_32_15 : Nat.choose 32 15 = 565722720 := by
  rw [Nat.choose_succ_succ, choose_val_31_14, choose_val_31_15]
theorem choose_val_32_16 : Nat.choose 32 16 = 601080390 := by
  rw [Nat.choose_succ_succ, choose_val_31_15, choose_val_31_16]
theorem choose_val_32_17 : Nat.choose 32 17 = 565722720 := by
  rw [Nat.choose_succ_succ, choose_val_31_16, choose_val_31_17]
theorem choose_val_32_18 : Nat.choose 32 18 = 471435600 := by
  rw [Nat.choose_succ_succ, choose_val_31_17, choose_val_31_18]
theorem choose_val_32_19 : Nat.choose 32 19 = 347373600 := by
  rw [Nat.choose_succ_succ, choose_val_31_18, choose_val_31_19]
theorem choose_val_32_20 : Nat.choose 32 20 = 225792840 := by
  rw [Nat.choose_succ_succ, choose_val_31_19, choose_val_31_20]
theorem choose_val_32_21 : Nat.choose 32 21 = 129024480 := by
  rw [Nat.choose_succ_succ, choose_val_31_20, choose_val_31_21]
theorem choose_val_32_22 : Nat.choose 32 22 = 64512240 := by
  rw [Nat.choose_succ_succ, choose_val_31_21, choose_val_31_22]
theorem choose_val_32_23 : Nat.choose 32 23 = 28048800 := by
  rw [Nat.choose_succ_succ, choose_val_31_22, choose_val_31_23]
theorem choose_val_32_24 : Nat.choose 32 24 = 10518300 := by
  rw [Nat.choose_succ_succ, choose_val_31_23, choose_val_31_24]
theorem choose_val_32_25 : Nat.choose 32 25 = 3365856 := by
  rw [Nat.choose_succ_succ, choose_val_31_24, choose_val_31_25]
theorem choose_val_32_26 : Nat.choose 32 26 = 906192 := by
  rw [Nat.choose_succ_succ, choose_val_31_25, choose_val_31_26]
theorem choose_val_32_27 : Nat.choose 32 27 = 201376 := by
  rw [Nat.choose_succ_succ, choose_val_31_26, choose_val_31_27]
theorem choose_val_32_28 : Nat.choose 32 28 = 35960 := by
  rw [Nat.choose_succ_succ, choose_val_31_27, choose_val_31_28]
theorem choose_val_32_29 : Nat.choose 32 29 = 4960 := by
  rw [Nat.choose_succ_succ, choose_val_31_28, choose_val_31_29]
theorem choose_val_32_30 : Nat.choose 32 30 = 496 := by
  rw [Nat.choose_succ_succ, choose_val_31_29, choose_val_31_30]
theorem choose_val_32_31 : Nat.choose 32 31 = 32 := by
  rw [Nat.choose_succ_succ, choose_val_31_30, choose_val_31_31]
theorem choose_val_32_32 : Nat.choose 32 32 = 1 := Nat.choose_self _
theorem bernoulli'_val_0 : bernoulli' 0 = 1 := by
  rw [bernoulli'_def]
  norm_num
theorem bernoulli'_val_1 : bernoulli' 1 = 1 / 2 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0]
theorem bernoulli'_val_2 : bernoulli' 2 = (1 / 6 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, choose_val_2_0, choose_val_2_1]
theorem bernoulli'_val_3 : bernoulli' 3 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨1, rfl⟩ (by norm_num)
theorem bernoulli'_val_4 : bernoulli' 4 = (-1 / 30 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, choose_val_4_0, choose_val_4_1, choose_val_4_2, choose_val_4_3]
theorem bernoulli'_val_5 : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
theorem bernoulli'_val_6 : bernoulli' 6 = (1 / 42 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, choose_val_6_0, choose_val_6_1, choose_val_6_2, choose_val_6_3, choose_val_6_4, choose_val_6_5]
theorem bernoulli'_val_7 : bernoulli' 7 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨3, rfl⟩ (by norm_num)
theorem bernoulli'_val_8 : bernoulli' 8 = (-1 / 30 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, choose_val_8_0, choose_val_8_1, choose_val_8_2, choose_val_8_3, choose_val_8_4, choose_val_8_5, choose_val_8_6, choose_val_8_7]
theorem bernoulli'_val_9 : bernoulli' 9 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨4, rfl⟩ (by norm_num)
theorem bernoulli'_val_10 : bernoulli' 10 = (5 / 66 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, choose_val_10_0, choose_val_10_1, choose_val_10_2, choose_val_10_3, choose_val_10_4, choose_val_10_5, choose_val_10_6, choose_val_10_7, choose_val_10_8, choose_val_10_9]
theorem bernoulli'_val_11 : bernoulli' 11 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨5, rfl⟩ (by norm_num)
theorem bernoulli'_val_12 : bernoulli' 12 = (-691 / 2730 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, bernoulli'_val_10, bernoulli'_val_11, choose_val_12_0, choose_val_12_1, choose_val_12_2, choose_val_12_3, choose_val_12_4, choose_val_12_5, choose_val_12_6, choose_val_12_7, choose_val_12_8, choose_val_12_9, choose_val_12_10, choose_val_12_11]
theorem bernoulli'_val_13 : bernoulli' 13 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨6, rfl⟩ (by norm_num)
theorem bernoulli'_val_14 : bernoulli' 14 = (7 / 6 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, bernoulli'_val_10, bernoulli'_val_11, bernoulli'_val_12, bernoulli'_val_13, choose_val_14_0, choose_val_14_1, choose_val_14_2, choose_val_14_3, choose_val_14_4, choose_val_14_5, choose_val_14_6, choose_val_14_7, choose_val_14_8, choose_val_14_9, choose_val_14_10, choose_val_14_11, choose_val_14_12, choose_val_14_13]
theorem bernoulli'_val_15 : bernoulli' 15 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨7, rfl⟩ (by norm_num)
theorem bernoulli'_val_16 : bernoulli' 16 = (-3617 / 510 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, bernoulli'_val_10, bernoulli'_val_11, bernoulli'_val_12, bernoulli'_val_13, bernoulli'_val_14, bernoulli'_val_15, choose_val_16_0, choose_val_16_1, choose_val_16_2, choose_val_16_3, choose_val_16_4, choose_val_16_5, choose_val_16_6, choose_val_16_7, choose_val_16_8, choose_val_16_9, choose_val_16_10, choose_val_16_11, choose_val_16_12, choose_val_16_13, choose_val_16_14, choose_val_16_15]
theorem bernoulli'_val_17 : bernoulli' 17 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨8, rfl⟩ (by norm_num)
theorem bernoulli'_val_18 : bernoulli' 18 = (43867 / 798 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, bernoulli'_val_10, bernoulli'_val_11, bernoulli'_val_12, bernoulli'_val_13, bernoulli'_val_14, bernoulli'_val_15, bernoulli'_val_16, bernoulli'_val_17, choose_val_18_0, choose_val_18_1, choose_val_18_2, choose_val_18_3, choose_val_18_4, choose_val_18_5, choose_val_18_6, choose_val_18_7, choose_val_18_8, choose_val_18_9, choose_val_18_10, choose_val_18_11, choose_val_18_12, choose_val_18_13, choose_val_18_14, choose_val_18_15, choose_val_18_16, choose_val_18_17]
theorem bernoulli'_val_19 : bernoulli' 19 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨9, rfl⟩ (by norm_num)
theorem bernoulli'_val_20 : bernoulli' 20 = (-174611 / 330 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, bernoulli'_val_10, bernoulli'_val_11, bernoulli'_val_12, bernoulli'_val_13, bernoulli'_val_14, bernoulli'_val_15, bernoulli'_val_16, bernoulli'_val_17, bernoulli'_val_18, bernoulli'_val_19, choose_val_20_0, choose_val_20_1, choose_val_20_2, choose_val_20_3, choose_val_20_4, choose_val_20_5, choose_val_20_6, choose_val_20_7, choose_val_20_8, choose_val_20_9, choose_val_20_10, choose_val_20_11, choose_val_20_12, choose_val_20_13, choose_val_20_14, choose_val_20_15, choose_val_20_16, choose_val_20_17, choose_val_20_18, choose_val_20_19]
theorem bernoulli'_val_21 : bernoulli' 21 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨10, rfl⟩ (by norm_num)
theorem bernoulli'_val_22 : bernoulli' 22 = (854513 / 138 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, bernoulli'_val_10, bernoulli'_val_11, bernoulli'_val_12, bernoulli'_val_13, bernoulli'_val_14, bernoulli'_val_15, bernoulli'_val_16, bernoulli'_val_17, bernoulli'_val_18, bernoulli'_val_19, bernoulli'_val_20, bernoulli'_val_21, choose_val_22_0, choose_val_22_1, choose_val_22_2, choose_val_22_3, choose_val_22_4, choose_val_22_5, choose_val_22_6, choose_val_22_7, choose_val_22_8, choose_val_22_9, choose_val_22_10, choose_val_22_11, choose_val_22_12, choose_val_22_13, choose_val_22_14, choose_val_22_15, choose_val_22_16, choose_val_22_17, choose_val_22_18, choose_val_22_19, choose_val_22_20, choose_val_22_21]
theorem bernoulli'_val_23 : bernoulli' 23 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨11, rfl⟩ (by norm_num)
theorem bernoulli'_val_24 : bernoulli' 24 = (-236364091 / 2730 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, bernoulli'_val_10, bernoulli'_val_11, bernoulli'_val_12, bernoulli'_val_13, bernoulli'_val_14, bernoulli'_val_15, bernoulli'_val_16, bernoulli'_val_17, bernoulli'_val_18, bernoulli'_val_19, bernoulli'_val_20, bernoulli'_val_21, bernoulli'_val_22, bernoulli'_val_23, choose_val_24_0, choose_val_24_1, choose_val_24_2, choose_val_24_3, choose_val_24_4, choose_val_24_5, choose_val_24_6, choose_val_24_7, choose_val_24_8, choose_val_24_9, choose_val_24_10, choose_val_24_11, choose_val_24_12, choose_val_24_13, choose_val_24_14, choose_val_24_15, choose_val_24_16, choose_val_24_17, choose_val_24_18, choose_val_24_19, choose_val_24_20, choose_val_24_21, choose_val_24_22, choose_val_24_23]
theorem bernoulli'_val_25 : bernoulli' 25 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨12, rfl⟩ (by norm_num)
theorem bernoulli'_val_26 : bernoulli' 26 = (8553103 / 6 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, bernoulli'_val_10, bernoulli'_val_11, bernoulli'_val_12, bernoulli'_val_13, bernoulli'_val_14, bernoulli'_val_15, bernoulli'_val_16, bernoulli'_val_17, bernoulli'_val_18, bernoulli'_val_19, bernoulli'_val_20, bernoulli'_val_21, bernoulli'_val_22, bernoulli'_val_23, bernoulli'_val_24, bernoulli'_val_25, choose_val_26_0, choose_val_26_1, choose_val_26_2, choose_val_26_3, choose_val_26_4, choose_val_26_5, choose_val_26_6, choose_val_26_7, choose_val_26_8, choose_val_26_9, choose_val_26_10, choose_val_26_11, choose_val_26_12, choose_val_26_13, choose_val_26_14, choose_val_26_15, choose_val_26_16, choose_val_26_17, choose_val_26_18, choose_val_26_19, choose_val_26_20, choose_val_26_21, choose_val_26_22, choose_val_26_23, choose_val_26_24, choose_val_26_25]
theorem bernoulli'_val_27 : bernoulli' 27 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨13, rfl⟩ (by norm_num)
theorem bernoulli'_val_28 : bernoulli' 28 = (-23749461029 / 870 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, bernoulli'_val_10, bernoulli'_val_11, bernoulli'_val_12, bernoulli'_val_13, bernoulli'_val_14, bernoulli'_val_15, bernoulli'_val_16, bernoulli'_val_17, bernoulli'_val_18, bernoulli'_val_19, bernoulli'_val_20, bernoulli'_val_21, bernoulli'_val_22, bernoulli'_val_23, bernoulli'_val_24, bernoulli'_val_25, bernoulli'_val_26, bernoulli'_val_27, choose_val_28_0, choose_val_28_1, choose_val_28_2, choose_val_28_3, choose_val_28_4, choose_val_28_5, choose_val_28_6, choose_val_28_7, choose_val_28_8, choose_val_28_9, choose_val_28_10, choose_val_28_11, choose_val_28_12, choose_val_28_13, choose_val_28_14, choose_val_28_15, choose_val_28_16, choose_val_28_17, choose_val_28_18, choose_val_28_19, choose_val_28_20, choose_val_28_21, choose_val_28_22, choose_val_28_23, choose_val_28_24, choose_val_28_25, choose_val_28_26, choose_val_28_27]
theorem bernoulli'_val_29 : bernoulli' 29 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨14, rfl⟩ (by norm_num)
theorem bernoulli'_val_30 : bernoulli' 30 = (8615841276005 / 14322 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, bernoulli'_val_10, bernoulli'_val_11, bernoulli'_val_12, bernoulli'_val_13, bernoulli'_val_14, bernoulli'_val_15, bernoulli'_val_16, bernoulli'_val_17, bernoulli'_val_18, bernoulli'_val_19, bernoulli'_val_20, bernoulli'_val_21, bernoulli'_val_22, bernoulli'_val_23, bernoulli'_val_24, bernoulli'_val_25, bernoulli'_val_26, bernoulli'_val_27, bernoulli'_val_28, bernoulli'_val_29, choose_val_30_0, choose_val_30_1, choose_val_30_2, choose_val_30_3, choose_val_30_4, choose_val_30_5, choose_val_30_6, choose_val_30_7, choose_val_30_8, choose_val_30_9, choose_val_30_10, choose_val_30_11, choose_val_30_12, choose_val_30_13, choose_val_30_14, choose_val_30_15, choose_val_30_16, choose_val_30_17, choose_val_30_18, choose_val_30_19, choose_val_30_20, choose_val_30_21, choose_val_30_22, choose_val_30_23, choose_val_30_24, choose_val_30_25, choose_val_30_26, choose_val_30_27, choose_val_30_28, choose_val_30_29]
theorem bernoulli'_val_31 : bernoulli' 31 = 0 :=
  bernoulli'_eq_zero_of_odd ⟨15, rfl⟩ (by norm_num)
theorem bernoulli'_val_32 : bernoulli' 32 = (-7709321041217 / 510 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_val_0, bernoulli'_val_1, bernoulli'_val_2, bernoulli'_val_3, bernoulli'_val_4, bernoulli'_val_5, bernoulli'_val_6, bernoulli'_val_7, bernoulli'_val_8, bernoulli'_val_9, bernoulli'_val_10, bernoulli'_val_11, bernoulli'_val_12, bernoulli'_val_13, bernoulli'_val_14, bernoulli'_val_15, bernoulli'_val_16, bernoulli'_val_17, bernoulli'_val_18, bernoulli'_val_19, bernoulli'_val_20, bernoulli'_val_21, bernoulli'_val_22, bernoulli'_val_23, bernoulli'_val_24, bernoulli'_val_25, bernoulli'_val_26, bernoulli'_val_27, bernoulli'_val_28, bernoulli'_val_29, bernoulli'_val_30, bernoulli'_val_31, choose_val_32_0, choose_val_32_1, choose_val_32_2, choose_val_32_3, choose_val_32_4, choose_val_32_5, choose_val_32_6, choose_val_32_7, choose_val_32_8, choose_val_32_9, choose_val_32_10, choose_val_32_11, choose_val_32_12, choose_val_32_13, choose_val_32_14, choose_val_32_15, choose_val_32_16, choose_val_32_17, choose_val_32_18, choose_val_32_19, choose_val_32_20, choose_val_32_21, choose_val_32_22, choose_val_32_23, choose_val_32_24, choose_val_32_25, choose_val_32_26, choose_val_32_27, choose_val_32_28, choose_val_32_29, choose_val_32_30, choose_val_32_31]

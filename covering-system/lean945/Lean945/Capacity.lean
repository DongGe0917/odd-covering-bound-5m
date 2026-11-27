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
import Lean945.Counting

open Finset

namespace Cover945

/-!
# L2: the general CRT capacity lemma

If `T ⊆ P` is pairwise coprime, every modulus of the pool `P` divides `N` and
is `≥ 2`, and the certificate inequality

  `∑ d ∈ P \ T, 1/d  <  ∏ d ∈ T, (1 - 1/d)`        `(★)`

holds, then no choice of one residue class per modulus from a subfamily
`S ⊆ P` covers `[0, N)`.

Proof (cf. `crt_notes.md` §2). Let `U = S ∩ T` and let `A` be the set of
points of `[0, N)` avoiding all classes with moduli in `U`. By CRT counting
(`card_avoid_prod` + `card_avoid_lift`), `|A| = (N / ∏ U) * ∏_{e ∈ U} (e - 1)`,
i.e. `(N : ℚ) * ∏_{e ∈ U} (1 - 1/e)`. Since `U ⊆ T` and every factor
`1 - 1/d` lies in `[0, 1]`, this is `≥ N * ∏_{d ∈ T} (1 - 1/d)`. On the other
hand every point of `A` must be covered by a class whose modulus lies in
`S \ U ⊆ P \ T`, and a class mod `d` covers exactly `N / d` points
(`card_filter_modEq`), so `|A| ≤ ∑_{d ∈ P \ T} N / d = N * ∑_{d ∈ P \ T} 1/d`,
contradicting `(★)`.
-/

/-- The product of a pairwise coprime family of divisors of `N` divides `N`. -/
lemma prod_dvd_of_pairwise {N : ℕ} (U : Finset ℕ) (hU : (U : Set ℕ).Pairwise Nat.Coprime)
    (hdvd : ∀ e ∈ U, e ∣ N) : ∏ e ∈ U, e ∣ N := by
  revert hU hdvd
  induction U using Finset.induction with
  | empty => intro _ _; simp
  | @insert d U' hdU' ih =>
    intro hU hdvd
    rw [Finset.prod_insert hdU']
    have hU' : (U' : Set ℕ).Pairwise Nat.Coprime :=
      fun x hx y hy hxy =>
        hU (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx)))
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hy))) hxy
    have hcop : Nat.Coprime d (∏ e ∈ U', e) :=
      Nat.coprime_prod_right_iff.mpr (fun e he =>
        hU (Finset.mem_coe.mpr (Finset.mem_insert_self d U'))
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem he)) (by
            rintro rfl
            exact hdU' he))
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd d (Finset.mem_insert_self d U'))
      (ih hU' (fun e he => hdvd e (Finset.mem_insert_of_mem he)))

/-- **L2 (capacity exclusion).** The CRT capacity certificate `(★)` excludes
    coverings of `[0, N)` by one residue class per modulus from `S`. -/
theorem capacity_exclusion {N : ℕ} (hN : 0 < N) {P S T : Finset ℕ}
    (hTP : T ⊆ P) (hSP : S ⊆ P) (hP : ∀ d ∈ P, d ∣ N ∧ 2 ≤ d)
    (hT : (T : Set ℕ).Pairwise Nat.Coprime) (r : ℕ → ℕ)
    (hcover : ∀ x < N, ∃ d ∈ S, x % d = r d % d)
    (hcert : ∑ d ∈ P \ T, (1 : ℚ) / d < ∏ d ∈ T, (1 - (1 : ℚ) / d)) :
    False := by
  classical
  set U := S ∩ T with hUdef
  have hUT : U ⊆ T := Finset.inter_subset_right
  have hUP : ∀ e ∈ U, e ∣ N ∧ 2 ≤ e :=
    fun e he => hP e (hSP (Finset.mem_of_mem_inter_left he))
  have hUcop : (U : Set ℕ).Pairwise Nat.Coprime :=
    fun x hx y hy hxy =>
      hT (Finset.mem_coe.mpr (hUT (Finset.mem_coe.mp hx)))
        (Finset.mem_coe.mpr (hUT (Finset.mem_coe.mp hy))) hxy
  have hprodU_dvd : ∏ e ∈ U, e ∣ N :=
    prod_dvd_of_pairwise U hUcop (fun e he => (hUP e he).1)
  have hprodU_pos : 0 < ∏ e ∈ U, e :=
    Finset.prod_pos (fun e he => by have := (hUP e he).2; omega)
  -- Step 1: the exact size of the avoided set `A`.
  have hA : (Finset.filter (fun x => ∀ e ∈ U, x % e ≠ r e % e) (Finset.range N)).card
      = (N / ∏ e ∈ U, e) * ∏ e ∈ U, (e - 1) := by
    rw [card_avoid_lift hprodU_pos hprodU_dvd U r (fun e he => Finset.dvd_prod_of_mem _ he),
      card_avoid_prod U (fun e he => (hUP e he).2) hUcop r]
  -- Step 2: covering forces `A` into the union of the `S \ U` classes.
  have hcoverA : Finset.filter (fun x => ∀ e ∈ U, x % e ≠ r e % e) (Finset.range N)
      ⊆ (S \ U).biUnion (fun d => Finset.filter (fun x => x % d = r d % d) (Finset.range N)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨d, hdS, hxd⟩ := hcover x hx.1
    have hdU : d ∉ U := fun hdU => hx.2 d hdU hxd
    rw [Finset.mem_biUnion]
    exact ⟨d, Finset.mem_sdiff.mpr ⟨hdS, hdU⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx.1, hxd⟩⟩
  have hcard : (Finset.filter (fun x => ∀ e ∈ U, x % e ≠ r e % e) (Finset.range N)).card
      ≤ ∑ d ∈ S \ U, (N / d) := by
    calc (Finset.filter (fun x => ∀ e ∈ U, x % e ≠ r e % e) (Finset.range N)).card
        ≤ ((S \ U).biUnion
            (fun d => Finset.filter (fun x => x % d = r d % d) (Finset.range N))).card :=
          Finset.card_le_card hcoverA
      _ ≤ ∑ d ∈ S \ U, (Finset.filter (fun x => x % d = r d % d) (Finset.range N)).card :=
          Finset.card_biUnion_le
      _ = ∑ d ∈ S \ U, (N / d) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdN : d ∣ N ∧ 2 ≤ d := hP d (hSP (Finset.mem_sdiff.mp hd).1)
          have hrw : Finset.range N = Finset.range (d * (N / d)) := by
            rw [Nat.mul_div_cancel' hdN.1]
          rw [hrw, card_filter_modEq d (N / d) (r d % d) (Nat.mod_lt _ (by omega))]
  -- Step 3: the rational inequality chain.
  have hcardQ : ((Finset.filter (fun x => ∀ e ∈ U, x % e ≠ r e % e) (Finset.range N)).card : ℚ)
      ≤ ∑ d ∈ S \ U, (N : ℚ) / d := by
    have h1 : ((Finset.filter (fun x => ∀ e ∈ U, x % e ≠ r e % e) (Finset.range N)).card : ℚ)
        ≤ ((∑ d ∈ S \ U, (N / d) : ℕ) : ℚ) := Nat.cast_le.mpr hcard
    refine h1.trans ?_
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun d _ => Nat.cast_div_le)
  have hprodU : ∏ e ∈ U, ((e : ℚ) - 1)
      = ((∏ e ∈ U, e : ℕ) : ℚ) * ∏ e ∈ U, (1 - (1 : ℚ) / e) := by
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e he
    have he0 : (e : ℚ) ≠ 0 := by
      exact_mod_cast (by have := (hUP e he).2; omega : e ≠ 0)
    rw [mul_sub, mul_one, mul_one_div_cancel he0]
  have hAQ : ((Finset.filter (fun x => ∀ e ∈ U, x % e ≠ r e % e) (Finset.range N)).card : ℚ)
      = (N : ℚ) * ∏ e ∈ U, (1 - (1 : ℚ) / e) := by
    have hcast : ((Finset.filter (fun x => ∀ e ∈ U, x % e ≠ r e % e) (Finset.range N)).card : ℚ)
        = ((N / ∏ e ∈ U, e : ℕ) : ℚ) * ∏ e ∈ U, ((e : ℚ) - 1) := by
      rw [hA, Nat.cast_mul, Nat.cast_prod]
      congr 1
      apply Finset.prod_congr rfl
      intro e he
      rw [Nat.cast_sub (by have := (hUP e he).2; omega : 1 ≤ e), Nat.cast_one]
    rw [hcast, hprodU, ← mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel hprodU_dvd]
  have hfac : ∀ d ∈ P, (0 : ℚ) ≤ 1 - (1 : ℚ) / d ∧ 1 - (1 : ℚ) / d ≤ 1 := by
    intro d hd
    have hd2 : 2 ≤ d := (hP d hd).2
    have hd0 : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    constructor
    · rw [sub_nonneg, div_le_one hd0]
      exact_mod_cast (by omega : 1 ≤ d)
    · exact sub_le_self 1 (by positivity)
  have hprodTU : ∏ d ∈ T, (1 - (1 : ℚ) / d) ≤ ∏ e ∈ U, (1 - (1 : ℚ) / e) := by
    have h1 : ∏ d ∈ T, (1 - (1 : ℚ) / d)
        = (∏ d ∈ T \ U, (1 - (1 : ℚ) / d)) * ∏ e ∈ U, (1 - (1 : ℚ) / e) :=
      (Finset.prod_sdiff hUT).symm
    have hX : (0 : ℚ) ≤ ∏ e ∈ U, (1 - (1 : ℚ) / e) :=
      Finset.prod_nonneg (fun e he => (hfac e (hSP (Finset.mem_of_mem_inter_left he))).1)
    have hY1 : ∏ d ∈ (T \ U : Finset ℕ), (1 - (1 : ℚ) / d) ≤ 1 := by
      have h := Finset.prod_le_prod₀ (s := T \ U)
        (f := fun (d : ℕ) => (1 - (1 : ℚ) / d))
        (g := fun _ => (1 : ℚ))
        (fun d hd => (hfac d (hTP (Finset.mem_sdiff.mp hd).1)).1)
        (fun d hd => (hfac d (hTP (Finset.mem_sdiff.mp hd).1)).2)
      simpa using h
    rw [h1]
    calc (∏ d ∈ T \ U, (1 - (1 : ℚ) / d)) * ∏ e ∈ U, (1 - (1 : ℚ) / e)
        ≤ 1 * ∏ e ∈ U, (1 - (1 : ℚ) / e) :=
          mul_le_mul_of_nonneg_right hY1 hX
      _ = ∏ e ∈ U, (1 - (1 : ℚ) / e) := one_mul _
  have hsub : S \ U ⊆ P \ T := by
    intro d hd
    rw [Finset.mem_sdiff] at hd ⊢
    exact ⟨hSP hd.1, fun hdT => hd.2 (Finset.mem_inter.mpr ⟨hd.1, hdT⟩)⟩
  have hsum : ∑ d ∈ S \ U, (N : ℚ) / d ≤ ∑ d ∈ P \ T, (N : ℚ) / d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
  have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
  have hfin : (N : ℚ) * ∏ d ∈ T, (1 - (1 : ℚ) / d)
      ≤ (N : ℚ) * ∑ d ∈ P \ T, (1 : ℚ) / d := by
    calc (N : ℚ) * ∏ d ∈ T, (1 - (1 : ℚ) / d)
        ≤ (N : ℚ) * ∏ e ∈ U, (1 - (1 : ℚ) / e) :=
          mul_le_mul_of_nonneg_left hprodTU hN0.le
      _ = ((Finset.filter (fun x => ∀ e ∈ U, x % e ≠ r e % e) (Finset.range N)).card : ℚ) :=
          hAQ.symm
      _ ≤ ∑ d ∈ S \ U, (N : ℚ) / d := hcardQ
      _ ≤ ∑ d ∈ P \ T, (N : ℚ) / d := hsum
      _ = (N : ℚ) * ∑ d ∈ P \ T, (1 : ℚ) / d := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun d _ => (mul_one_div _ _).symm)
  have hlt := mul_lt_mul_of_pos_left hcert hN0
  exact absurd (lt_of_lt_of_le hlt hfin) (lt_irrefl _)

end Cover945

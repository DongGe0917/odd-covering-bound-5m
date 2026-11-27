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
# Counting lemmas for the capacity argument

Three exact counting facts, all proved by explicit bijections
(`Finset.card_bij'`), plus the product formula obtained by induction:

* `card_filter_modEq`: one residue class mod `d` meets `[0, d*k)` in `k` points.
* `card_avoid_lift`: avoidance counts lift from `[0, M)` to `[0, N)` when `M ∣ N`.
* `card_avoid_insert`: the CRT step — adjoining a modulus `d` coprime to `M'`
  multiplies the avoidance count by `d - 1`.
* `card_avoid_prod`: for a pairwise coprime family `U`, the number of points of
  `[0, ∏ U)` avoiding a chosen residue class for every `e ∈ U` is `∏ (e - 1)`.
-/

/-- **Counting A.** A single residue class mod `d` meets `[0, d * k)` in
    exactly `k` points. Bijection: `x ↦ (x / d, r)`, inverse `(q, r) ↦ q * d + r`. -/
lemma card_filter_modEq (d k r : ℕ) (hr : r < d) :
    (Finset.filter (fun x => x % d = r) (Finset.range (d * k))).card = k := by
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hr
  have hbij := Finset.card_bij'
    (s := Finset.filter (fun x => x % d = r) (Finset.range (d * k)))
    (t := Finset.range k ×ˢ {r})
    (i := fun x _ => (x / d, r))
    (j := fun p _ => p.1 * d + p.2)
    (by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_singleton_self r⟩
      show x / d < k
      rw [Nat.div_lt_iff_lt_mul hd, mul_comm]
      exact hx.1)
    (by
      intro p hp
      obtain ⟨q, s⟩ := p
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hp
      obtain ⟨hq, hs⟩ := hp
      subst hs
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · show q * d + s < d * k
        calc q * d + s < (q + 1) * d := by
              rw [add_mul, one_mul]
              exact Nat.add_lt_add_left hr _
          _ ≤ k * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hq)
          _ = d * k := mul_comm _ _
      · show (q * d + s) % d = s
        have hrw : q * d + s = s + d * q := by ring
        rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr])
    (by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      show (x / d) * d + r = x
      rw [← hx.2, mul_comm]
      exact Nat.div_add_mod x d)
    (by
      intro p hp
      obtain ⟨q, s⟩ := p
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hp
      obtain ⟨hq, hs⟩ := hp
      subst hs
      refine Prod.ext ?_ rfl
      show (q * d + s) / d = q
      have hrw : q * d + s = s + q * d := by ring
      rw [hrw, mul_comm q d, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hr, zero_add])
  rw [hbij, Finset.card_product, Finset.card_range, Finset.card_singleton, mul_one]

/-- **Counting D (lift).** If `M ∣ N` and every `e ∈ U` divides `M`, then the
    number of points of `[0, N)` avoiding the chosen classes mod `e ∈ U` is
    `N / M` times the corresponding count over `[0, M)`.
    Bijection: `x ↦ (x / M, x % M)`, inverse `(q, y) ↦ q * M + y`. -/
lemma card_avoid_lift {M N : ℕ} (hM : 0 < M) (hdiv : M ∣ N) (U : Finset ℕ) (a : ℕ → ℕ)
    (hUdiv : ∀ e ∈ U, e ∣ M) :
    (Finset.filter (fun x => ∀ e ∈ U, x % e ≠ a e % e) (Finset.range N)).card
      = (N / M) * (Finset.filter (fun y => ∀ e ∈ U, y % e ≠ a e % e) (Finset.range M)).card := by
  have hbij := Finset.card_bij'
    (s := Finset.filter (fun x => ∀ e ∈ U, x % e ≠ a e % e) (Finset.range N))
    (t := Finset.range (N / M) ×ˢ Finset.filter (fun y => ∀ e ∈ U, y % e ≠ a e % e) (Finset.range M))
    (i := fun x _ => (x / M, x % M))
    (j := fun p _ => p.1 * M + p.2)
    (by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hM), ?_⟩⟩
      · show x / M < N / M
        have hNM : (N / M) * M = N := Nat.div_mul_cancel hdiv
        rw [Nat.div_lt_iff_lt_mul hM, hNM]
        exact hx.1
      · show ∀ e ∈ U, (x % M) % e ≠ a e % e
        intro e he
        rw [Nat.mod_mod_of_dvd x (hUdiv e he)]
        exact hx.2 e he)
    (by
      intro p hp
      rw [Finset.mem_product, Finset.mem_range] at hp
      obtain ⟨hq, hp2⟩ := hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp2
      obtain ⟨hp2lt, hp2av⟩ := hp2
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · show p.1 * M + p.2 < N
        calc p.1 * M + p.2 < (p.1 + 1) * M := by
              rw [add_mul, one_mul]
              exact Nat.add_lt_add_left hp2lt _
          _ ≤ (N / M) * M := Nat.mul_le_mul_right M (Nat.succ_le_of_lt hq)
          _ = N := Nat.div_mul_cancel hdiv
      · intro e he
        obtain ⟨c, hc⟩ := hUdiv e he
        have hmod : (p.1 * M + p.2) % e = p.2 % e := by
          have hrw : p.1 * M + p.2 = p.2 + e * (p.1 * c) := by rw [hc]; ring
          rw [hrw, Nat.add_mul_mod_self_left]
        rw [hmod]
        exact hp2av e he)
    (by
      intro x _
      show (x / M) * M + x % M = x
      rw [mul_comm]
      exact Nat.div_add_mod x M)
    (by
      intro p hp
      rw [Finset.mem_product, Finset.mem_range] at hp
      obtain ⟨hq, hp2⟩ := hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp2
      obtain ⟨hp2lt, -⟩ := hp2
      refine Prod.ext ?_ ?_
      · show (p.1 * M + p.2) / M = p.1
        have hrw : p.1 * M + p.2 = p.2 + p.1 * M := by ring
        rw [hrw, mul_comm p.1 M, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hp2lt,
          zero_add]
      · show (p.1 * M + p.2) % M = p.2
        have hrw : p.1 * M + p.2 = p.2 + M * p.1 := by ring
        rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp2lt])
  rw [hbij, Finset.card_product, Finset.card_range]

/-- **Counting B (CRT step).** Adjoining a modulus `d ≥ 2` coprime to `M'`
    multiplies the avoidance count by `d - 1`. The inverse map is the Chinese
    remainder construction `Nat.chineseRemainder`. -/
lemma card_avoid_insert {d M' : ℕ} (hd : 2 ≤ d) (hM' : 0 < M') (hcop : Nat.Coprime d M')
    (U' : Finset ℕ) (a : ℕ → ℕ) (hdiv : ∀ e ∈ U', e ∣ M') :
    (Finset.filter (fun x => x % d ≠ a d % d ∧ ∀ e ∈ U', x % e ≠ a e % e)
        (Finset.range (d * M'))).card
      = (d - 1) * (Finset.filter (fun y => ∀ e ∈ U', y % e ≠ a e % e) (Finset.range M')).card := by
  have hd0 : 0 < d := by omega
  have hbij := Finset.card_bij'
    (s := Finset.filter (fun x => x % d ≠ a d % d ∧ ∀ e ∈ U', x % e ≠ a e % e)
        (Finset.range (d * M')))
    (t := (Finset.filter (fun u => u ≠ a d % d) (Finset.range d))
        ×ˢ Finset.filter (fun y => ∀ e ∈ U', y % e ≠ a e % e) (Finset.range M'))
    (i := fun x _ => (x % d, x % M'))
    (j := fun p _ => (Nat.chineseRemainder hcop p.1 p.2 : ℕ) % (d * M'))
    (by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      refine Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hd0), hx.2.1⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hM'), ?_⟩⟩
      show ∀ e ∈ U', (x % M') % e ≠ a e % e
      intro e he
      rw [Nat.mod_mod_of_dvd x (hdiv e he)]
      exact hx.2.2 e he)
    (by
      intro p hp
      rw [Finset.mem_product] at hp
      obtain ⟨hp1, hp2⟩ := hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp1 hp2
      obtain ⟨hp1lt, hp1ne⟩ := hp1
      obtain ⟨hp2lt, hp2av⟩ := hp2
      set z := (Nat.chineseRemainder hcop p.1 p.2 : ℕ) with hz
      have hz1 : z % d = p.1 % d := (Nat.chineseRemainder hcop p.1 p.2).2.1
      have hz2 : z % M' = p.2 % M' := (Nat.chineseRemainder hcop p.1 p.2).2.2
      have hxd : (z % (d * M')) % d = p.1 := by
        rw [Nat.mod_mod_of_dvd z (dvd_mul_right d M'), hz1, Nat.mod_eq_of_lt hp1lt]
      have hxM : (z % (d * M')) % M' = p.2 := by
        rw [Nat.mod_mod_of_dvd z (dvd_mul_left M' d), hz2, Nat.mod_eq_of_lt hp2lt]
      have hne : (z % (d * M')) % d ≠ a d % d := by
        rw [hxd]
        exact hp1ne
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos hd0 hM')),
        hne, ?_⟩
      intro e he
      have h1' : (z % (d * M')) % e = z % e :=
        Nat.mod_mod_of_dvd z (dvd_trans (hdiv e he) (dvd_mul_left M' d))
      have h2' : z % e = p.2 % e := by
        rw [← Nat.mod_mod_of_dvd z (hdiv e he), hz2, Nat.mod_mod_of_dvd p.2 (hdiv e he)]
      rw [h1', h2']
      exact hp2av e he)
    (by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      show (Nat.chineseRemainder hcop (x % d) (x % M') : ℕ) % (d * M') = x
      have huniq := Nat.chineseRemainder_modEq_unique hcop
        (a := x % d) (b := x % M') (z := x)
        (Nat.mod_modEq x d).symm (Nat.mod_modEq x M').symm
      have hmod : x % (d * M')
          = (Nat.chineseRemainder hcop (x % d) (x % M') : ℕ) % (d * M') := huniq
      rw [Nat.mod_eq_of_lt hx.1] at hmod
      exact hmod.symm)
    (by
      intro p hp
      rw [Finset.mem_product] at hp
      obtain ⟨hp1, hp2⟩ := hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp1 hp2
      obtain ⟨hp1lt, -⟩ := hp1
      obtain ⟨hp2lt, -⟩ := hp2
      set z := (Nat.chineseRemainder hcop p.1 p.2 : ℕ) with hz
      have hz1 : z % d = p.1 % d := (Nat.chineseRemainder hcop p.1 p.2).2.1
      have hz2 : z % M' = p.2 % M' := (Nat.chineseRemainder hcop p.1 p.2).2.2
      refine Prod.ext ?_ ?_
      · show (z % (d * M')) % d = p.1
        rw [Nat.mod_mod_of_dvd z (dvd_mul_right d M'), hz1, Nat.mod_eq_of_lt hp1lt]
      · show (z % (d * M')) % M' = p.2
        rw [Nat.mod_mod_of_dvd z (dvd_mul_left M' d), hz2, Nat.mod_eq_of_lt hp2lt])
  rw [hbij, Finset.card_product, Finset.filter_ne', Finset.card_erase_of_mem
      (Finset.mem_range.mpr (Nat.mod_lt _ hd0)), Finset.card_range]

/-- **Counting C (product formula).** For a pairwise coprime family `U` of
    moduli `≥ 2`, the number of points of `[0, ∏ U)` avoiding one chosen
    residue class for every `e ∈ U` is exactly `∏ e ∈ U, (e - 1)`. -/
lemma card_avoid_prod (U : Finset ℕ) (hU2 : ∀ e ∈ U, 2 ≤ e)
    (hU : (U : Set ℕ).Pairwise Nat.Coprime)
    (a : ℕ → ℕ) :
    (Finset.filter (fun x => ∀ e ∈ U, x % e ≠ a e % e) (Finset.range (∏ d ∈ U, d))).card
      = ∏ d ∈ U, (d - 1) := by
  revert hU2 hU
  induction U using Finset.induction with
  | empty => intro _ _; simp
  | @insert d U' hdU' ih =>
    intro hU2 hU
    have hd2 : 2 ≤ d := hU2 d (Finset.mem_insert_self d U')
    have hU'2 : ∀ e ∈ U', 2 ≤ e := fun e he => hU2 e (Finset.mem_insert_of_mem he)
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
    have hM' : 0 < ∏ e ∈ U', e :=
      Finset.prod_pos (fun e he => by have := hU'2 e he; omega)
    have hsplit : (Finset.filter (fun x => ∀ e ∈ insert d U', x % e ≠ a e % e)
          (Finset.range (∏ e ∈ insert d U', e))).card
        = (Finset.filter (fun x => x % d ≠ a d % d ∧ ∀ e ∈ U', x % e ≠ a e % e)
            (Finset.range (d * ∏ e ∈ U', e))).card := by
      rw [Finset.prod_insert hdU']
      congr 1
      exact Finset.filter_congr (fun x _ => Finset.forall_mem_insert d U' _)
    rw [hsplit, card_avoid_insert hd2 hM' hcop U' a (fun e he => Finset.dvd_prod_of_mem _ he),
      ih hU'2 hU', Finset.prod_insert hdU']

end Cover945

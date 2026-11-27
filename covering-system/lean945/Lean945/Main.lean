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
import Lean945.Basic
import Lean945.Counting
import Lean945.Capacity

open Finset

namespace Cover945

/-!
# L3: assembly — no odd distinct-moduli covering system with lcm dividing 945

A covering system of `ℤ` with all moduli dividing 945 restricts to a covering
of `[0, 945)` by one residue class per modulus (distinctness is used exactly
here: the residue attached to a modulus is well defined). Its modulus set is
contained in the pool `P(945)`, so the capacity lemma `capacity_exclusion`
applies with the certificate `T = {3, 5, 7}` verified in `Basic.lean`.

Note: the proof does not use the oddness hypothesis — the capacity
certificate for `N = 945` excludes *every* covering by distinct moduli
dividing 945. Oddness is part of the Erdős #7 statement and is kept in the
hypotheses for fidelity with `命题与约束.md`.
-/

/-- **Main theorem.** There is no covering system of `ℤ` whose moduli are
    pairwise distinct, all odd, all `> 1`, and whose lcm divides `945`. -/
theorem no_odd_covering_lcm_dvd_945 :
    ¬ ∃ (ι : Type) (inst : Fintype ι) (n : ι → ℕ) (a : ι → ℤ),
      (∀ i, 1 < n i) ∧ (∀ i, Odd (n i)) ∧ Function.Injective n ∧
      ((@Finset.univ ι inst).lcm n) ∣ 945 ∧
      (∀ z : ℤ, ∃ i, z ≡ a i [ZMOD (n i : ℤ)]) := by
  rintro ⟨ι, instF, n, a, hgt, _hodd, hinj, hlcm, hcover⟩
  classical
  letI := instF
  -- Every modulus divides 945 (it divides the lcm, which divides 945).
  have hdiv : ∀ i, n i ∣ 945 :=
    fun i => dvd_trans (Finset.dvd_lcm (Finset.mem_univ i)) hlcm
  -- Choose, for every modulus `d` in the image of `n`, the canonical residue
  -- of the (unique, by injectivity) representing class.
  obtain ⟨r, hr_spec⟩ : ∃ r : ℕ → ℕ, ∀ i, ((a i % (n i : ℤ)).toNat) = r (n i)
      ∧ r (n i) < n i := by
    refine ⟨fun d => if h : ∃ j, n j = d then ((a (Classical.choose h) % (d : ℤ)).toNat) else 0,
      fun i => ?_⟩
    have hexd : ∃ j, n j = n i := ⟨i, rfl⟩
    have hchoose : Classical.choose hexd = i := by
      apply hinj
      exact Classical.choose_spec hexd
    have hni : (0 : ℤ) < (n i : ℤ) := by
      exact_mod_cast (show 0 < n i by have := hgt i; omega)
    have htoNat : ((a i % (n i : ℤ)).toNat : ℤ) = a i % (n i : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hni))
    constructor
    · show (a i % (n i : ℤ)).toNat
        = (if h : ∃ j, n j = n i then ((a (Classical.choose h) % (n i : ℤ)).toNat) else 0)
      rw [dif_pos hexd, hchoose]
    · show (if h : ∃ j, n j = n i then ((a (Classical.choose h) % (n i : ℤ)).toNat) else 0)
        < n i
      rw [dif_pos hexd, hchoose]
      have hlt : a i % (n i : ℤ) < (n i : ℤ) := Int.emod_lt_of_pos _ hni
      exact_mod_cast (htoNat ▸ hlt)
  -- The chosen residues describe the same classes as the original data.
  have hr : ∀ i, ∀ x : ℕ, (x : ℤ) ≡ a i [ZMOD (n i : ℤ)] → x % (n i) = r (n i) % (n i) := by
    intro i x hx
    obtain ⟨heq, hlt⟩ := hr_spec i
    have hni0 : (n i : ℤ) ≠ 0 := by
      exact_mod_cast (show n i ≠ 0 by have := hgt i; omega)
    have h1 : ((x % (n i) : ℕ) : ℤ) = ((r (n i) : ℕ) : ℤ) := by
      rw [Int.natCast_mod, ← heq,
        Int.toNat_of_nonneg (Int.emod_nonneg _ hni0)]
      exact hx
    have h2 : x % (n i) = r (n i) := Nat.cast_inj.mp h1
    rw [h2, Nat.mod_eq_of_lt hlt]
  -- Hence the classes cover `[0, 945)`.
  have hcover' : ∀ x < 945, ∃ d ∈ Finset.univ.image n, x % d = r d % d := by
    intro x _
    obtain ⟨i, hi⟩ := hcover (x : ℤ)
    exact ⟨n i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hr i x hi⟩
  -- Apply the capacity lemma with the 945 certificate.
  exact capacity_exclusion (by norm_num : 0 < 945) certT_subset_pool945
    (by
      intro d hd
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hd
      rw [← hi]
      exact mem_pool945 (hdiv i) (hgt i))
    (fun d hd => pool945_dvd hd) certT_pairwise r hcover' cert_inequality

#print axioms no_odd_covering_lcm_dvd_945

end Cover945

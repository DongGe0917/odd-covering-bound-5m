import Mathlib.Tactic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic

/-!
# L3: Erdős Problem 366 cluster

Source problem (lefttosolve.com, difficulty 37/100): "Erdős Problem 366 —
weaker", the open question whether there are consecutive 3-full integers:
  `∃ n > 0, (3).Full n ∧ (3).Full (n + 1)`
The original statement is *not* claimed here.

`Nat.Full` below is the same definition as upstream formal-conjectures
(`FormalConjecturesForMathlib/Data/Nat/Full.lean`):
`k.Full n ↔ ∀ p ∈ n.primeFactors, p ^ k ∣ n`.

This file contains:
* (a) two known results stated alongside the problem upstream: a sanity
  statement with witness 8, and Golomb's solved variant with witness
  12167 = 23^3, 12168 = 2^3 * 3^2 * 13^2;
* (b) a bounded finite variant of the open weaker statement: there is no
  pair of consecutive 3-full integers `n, n + 1` with `1 ≤ n ≤ 200`
  (a Python sieve found none below 2,000,000; the sieve was cross-validated
  against brute-force factorisation below 5000). Note the pair (0, 1) is
  vacuously 3-full under this definition (`primeFactors 0 = primeFactors 1 = ∅`),
  which is why the bound starts at 1, matching the `n > 0` in the original.

Proof methods: (a) uses the same `primeFactorsEq` simproc + `norm_num`
approach as upstream (kernel `decide` cannot reduce `Nat.primeFactors`,
which is defined by well-founded recursion). (b) uses `native_decide`
(native evaluation handles the recursion); it therefore depends on
`Lean.ofReduceBool`, as recorded in `进展-L.md`.
-/

namespace Nat

/-- `n` is `k`-full if every prime factor `p` of `n` satisfies `p ^ k ∣ n`.
    (Same definition as upstream formal-conjectures.) -/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

instance Full.decide : ∀ k n, Decidable (Full k n) := by
  intro k n
  dsimp [Full]
  infer_instance

end Nat

open Lean Meta Qq in
/-- Simproc to compute `Nat.primeFactors` (same as upstream
    formal-conjectures, `FormalConjecturesForMathlib/Data/Nat/Full.lean`). -/
dsimproc primeFactorsEq (Nat.primeFactors _) := fun e ↦ do
  unless e.isAppOfArity `Nat.primeFactors 1 do return .continue
  let some n ← Lean.Nat.fromExpr? e.appArg! | return .continue
  let outAsList : List Q(ℕ) := (unsafe n.primeFactors.val.unquot).map mkNatLit
  let outAsFinset : Q(Finset ℕ) := outAsList.foldl (fun s n ↦ q(insert $n $s)) q({})
  return .done outAsFinset

/-- (a) Known: 8 is 3-full and 9 is 2-full. -/
theorem exists_three_full_then_two_full :
    ∃ n > 0, (3).Full n ∧ (2).Full (n + 1) := by
  use 8
  norm_num +contextual [Nat.Full, Nat.primeFactors, Nat.primeFactorsList]

/-- (a) Known (Golomb): (8, 9) is not the only pair of consecutive integers
with `n` 3-full and `n + 1` 2-full; (12167, 12168) is another. -/
theorem erdos_366_variants_three_two :
    ¬ ∀ n > 0, (3).Full n ∧ (2).Full (n + 1) → n = 8 := by
  intro h
  have hcon : (3).Full 12167 ∧ (2).Full (12167 + 1) := by
    norm_num +contextual [Nat.Full, Nat.primeFactors, Nat.primeFactorsList]
  have h8 := h 12167 (by norm_num) hcon
  norm_num at h8

/-- (b) Bounded finite variant of the open "weaker" statement:
no pair of consecutive 3-full integers `n, n + 1` with `1 ≤ n ≤ 200`.
Proved by `native_decide`; depends on `Lean.ofReduceBool`. -/
theorem no_consecutive_three_full_between_1_200 :
    ∀ n < 200, ¬ ((3).Full (n + 1) ∧ (3).Full (n + 2)) := by
  native_decide

#print axioms exists_three_full_then_two_full
#print axioms erdos_366_variants_three_two
#print axioms no_consecutive_three_full_between_1_200

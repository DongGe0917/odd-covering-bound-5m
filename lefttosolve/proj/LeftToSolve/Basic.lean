import Mathlib.Data.Int.Basic

/-- Warmup sanity check (toolchain smoke test). -/
example : (37 : ℤ) ∣ (68987104985387322546457 : ℤ) * 37 := ⟨_, Int.mul_comm _ _⟩

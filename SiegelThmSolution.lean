/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import SiegelThm.Main

/-!
# Proofs of the statements in `SiegelThmChallenge.lean`

Goldfeld's proof (1974) of Siegel's theorem, Mathlib only: see `SiegelThm/Main.lean`
(dichotomy), `SiegelThm/Goldfeld2.lean` (Goldfeld's lemma, Taylor expansion at `2`),
`SiegelThm/Integral.lean` (integral representation).
-/

@[expose] public section

namespace SiegelThm

/-- **Siegel's theorem.** -/
theorem siegel : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      c * (N : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖ :=
  SiegelThmLib.siegel

/-- The integral representation of `L(s, χ)` on `Re s > 0`. -/
theorem LFunction_eq_integral : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ s : ℂ, 0 < s.re →
      DirichletCharacter.LFunction χ s =
        s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)) :=
  SiegelThmLib.LFunction_eq_integral

/-- Partial sums of a non-principal character are bounded by the modulus. -/
theorem norm_sum_Icc_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (M : ℕ) : ‖∑ k ∈ Finset.Icc 1 M, χ k‖ ≤ N :=
  SiegelThmLib.norm_sum_Icc_le hχ M

end SiegelThm

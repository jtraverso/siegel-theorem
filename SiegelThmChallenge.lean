/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Siegel's theorem (1935)

For every `ε > 0` there is `c(ε) > 0` such that `|L(1, χ)| ≥ c(ε) N^{-ε}` for every real
(quadratic) non-principal Dirichlet character `χ` modulo `N` (C. L. Siegel, *Über die
Classenzahl quadratischer Zahlkörper*, Acta Arith. 1 (1935)). Together with two auxiliary
statements: the integral representation `L(s, χ) = s ∫_1^∞ A(t) t^{-s-1} dt` on `Re s > 0`,
`A(t) = ∑_{1 ≤ k ≤ t} χ(k)`, and the bound `|∑_{k=1}^{M} χ(k)| ≤ N`.
-/

@[expose] public section

namespace SiegelThm

/-- **Siegel's theorem.** -/
theorem siegel : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      c * (N : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  sorry

/-- The integral representation of `L(s, χ)` on `Re s > 0`. -/
theorem LFunction_eq_integral : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ s : ℂ, 0 < s.re →
      DirichletCharacter.LFunction χ s =
        s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)) := by
  sorry

/-- Partial sums of a non-principal character are bounded by the modulus. -/
theorem norm_sum_Icc_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (M : ℕ) : ‖∑ k ∈ Finset.Icc 1 M, χ k‖ ≤ N := by
  sorry

end SiegelThm

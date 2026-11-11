# Siegel's theorem in Lean 4 / Mathlib

A self-contained Lean 4 / Mathlib formalization of **Siegel's theorem** (1935): for every
`ε > 0` there is `c(ε) > 0` such that

`‖L(1, χ)‖ ≥ c(ε) · N^(-ε)`

for every real (quadratic, `χ ^ 2 = 1`) non-principal Dirichlet character `χ` modulo `N`,
with Mathlib's `DirichletCharacter.LFunction`. The proof is Goldfeld's (1974): the auxiliary
function `F = ζ · L(χ₁) · L(χ₂) · L(χ₁χ₂)` has non-negative Dirichlet coefficients, and a
Taylor expansion of its regular part at `s = 2` with Cauchy's estimates on the circle
`|s - 2| = 3/2` gives `F(β) ≥ 1/2 - C λ (1-β)^(-1) (N₁N₂)^(C(1-β))`; the dichotomy on the
existence of an exceptional zero then gives the (ineffective) constant. Non-primitive
characters are handled directly (no reduction to primitive characters is needed).

Compared statements (`SiegelThmChallenge.lean`, namespace `SiegelThm`):

* `SiegelThm.siegel` — Siegel's theorem;
* `SiegelThm.LFunction_eq_integral` — `L(s, χ) = s ∫_1^∞ A(t) t^(-s-1) dt` for `Re s > 0`,
  `χ ≠ 1`, `A(t) = ∑_{1 ≤ k ≤ t} χ(k)`;
* `SiegelThm.norm_sum_Icc_le` — `‖∑_{k=1}^M χ(k)‖ ≤ N` for `χ ≠ 1`.

Dependencies: Mathlib only (`v4.35.0-rc3`). The proof plan with explicit constants is in
`NOTES.md`.

Build: `lake build`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

License: Apache 2.0.

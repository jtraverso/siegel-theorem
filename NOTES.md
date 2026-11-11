# Siegel's theorem — proof plan (Goldfeld 1974), constants explicit

Mathlib-only, independent code (no LeanLab/goldbach-lean source consulted; only the three
statements, which H1 uses as hypotheses, are matched verbatim).

Targets (namespace `SiegelThm`):
* `norm_sum_Icc_le` : `χ ≠ 1 → ‖∑ k ∈ Icc 1 M, χ k‖ ≤ N`.
* `LFunction_eq_integral` : `L(s,χ) = s ∫_{t>1} A_χ(t) t^{-(s+1)}` for `Re s > 0`, `χ ≠ 1`,
  `A_χ(t) = ∑_{1 ≤ k ≤ ⌊t⌋} χ k`.
* `siegel` : `∀ ε > 0, ∃ c > 0, ∀ N χ, χ ≠ 1 → χ^2 = 1 → c N^{-ε} ≤ ‖L(1,χ)‖`.

Notation: `χ` mod `N` (`NeZero N`), `σ = Re s`.

## 1. Character sums (`SiegelThm/CharSum.lean`)
`∑_{k=a+1}^{a+N} χ k = 0` (a complete residue system, `MulChar.sum_eq_zero_of_ne_one`), so
`S(M+N) = S(M)`; for `M < N`, `|S(M)| ≤ M`. Hence `|S(M)| ≤ N` (strong induction).
Real characters (`χ^2 = 1`) take values in `{0, 1, -1}` (`MulChar.isQuadratic_iff_sq_eq_one`).

## 2. Integral transforms (`SiegelThm/Integral.lean`)
For `g` measurable with `‖g‖ ≤ B` on `(1,∞)`: `J_g(s) = ∫_{t>1} g(t) t^{-(s+1)}`.
* integrable for `σ > 0`, `‖J_g(s)‖ ≤ B/σ` (`∫_1^∞ t^{-σ-1} = 1/σ`);
* holomorphic on `σ > 0`: `J_g(s) = mellin (1_{(1,∞)} g) (-s)`,
  `mellin_differentiableAt_of_isBigO_rpow` with `a = 0` (bounded at ∞), anything at 0.
* (T2) For `σ > 1`: Mathlib `LSeries_eq_mul_integral` (Abel summation, `r = 0` by §1) and
  `LFunction_eq_LSeries`. Both sides holomorphic on the convex half-plane `σ > 0`
  (`differentiable_LFunction`), agree on `σ > 1` ⇒ equal (identity theorem,
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`).
* Bounds: `|L(s,χ)| ≤ |s| N / σ` (σ > 0); in particular `|L(1,χ)| ≤ N`.
  Log-type bound: `|A(t)| ≤ min(t, N) ≤ t^{1-η} N^η`, so `|L(1,χ)| ≤ N^η / η` (0 < η < 1).
* ζ without Mathlib's continuation: for `σ > 1`, `∑ n^{-s} = s∫⌊t⌋t^{-s-1}` (Abel summation with
  `f = 1`, `r = 1`) `= 1/(s-1) + H(s)`, `H(s) := 1 - s J_{fract}(s)`; `H` is holomorphic on
  `σ > 0`, `|H(s)| ≤ 1 + |s|/σ`, and for real `β ∈ (0,1)`, `H(β)` is real and `≤ 1`.

## 3. Coefficients (`SiegelThm/Coeff.lean`)
`χ₁` mod `N₁`, `χ₂` mod `N₂` real non-principal, `Q = N₁N₂`,
`ψ = changeLevel χ₁ · changeLevel χ₂` (mod Q), `ψ n = χ₁ n · χ₂ n` for all `n : ℕ`.
`a = ζ * χ₁ * χ₂ * ψ` (Dirichlet convolution), multiplicative, `a 1 = 1`, `a ≥ 0`:
at `p^k` with `x = χ₁ p`, `y = χ₂ p` ∈ {0, ±1}: `a = (ζ*χ₁) * (χ₂*ψ) = (ζ*χ₂) * (χ₁*ψ)`;
`ζ*χᵢ ≥ 0` (Mathlib `zetaMul_nonneg`); `(χ₂*ψ)(p^j) = ∑_{t≤j} y^t (xy)^{j-t} ≥ 0` unless
`y = -1, x ∈ {0,1}`, in which case `(χ₁*ψ)(p^j) = ∑ x^t (xy)^{j-t} ≥ 0`.
For `σ > 1`: `LSeries a s = ζ(s) L(s,χ₁) L(s,χ₂) L(s,ψ)` (`LSeries_convolution'`).

## 4. Goldfeld's lemma (`SiegelThm/Goldfeld.lean`) — HARDEST STEP
Assume `ψ ≠ 1`. `P = L(·,χ₁)L(·,χ₂)L(·,ψ)` (entire), `λ = P(1)`,
`G = dslope P 1 + H·P` (holomorphic on `σ > 0`), `F(s) = (1/(s-1) + H(s)) P(s)`;
`F = G + λ/(s-1)` for `s ≠ 1`, `F = LSeries a` on `σ > 1`.
* Circle `|s-2| = 3/2`: `σ ≥ 1/2`, `|s| ≤ 7/2`, `|s-1| ≥ 1/2`; `|L| ≤ 7N`; `|P| ≤ 343Q²`,
  `|λ| ≤ Q²`, `|dslope P 1| ≤ 2(343+1)Q²`, `|H| ≤ 8`; so `|G| ≤ 4000 Q²` =: `M_G`.
* Cauchy (`norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, R = 3/2):
  `|G⁽ⁿ⁾(2)| ≤ n! M_G (2/3)^n`.
* `G⁽ⁿ⁾(2) = (LSeries a)⁽ⁿ⁾(2) − λ(−1)ⁿ n!` (`iter_deriv_inv_linear_sub`, `iteratedDeriv_sub`,
  `Set.EqOn.iteratedDeriv_of_isOpen`), and `Dₙ := (−1)ⁿ (LSeries a)⁽ⁿ⁾(2) ≥ 0`
  (`LSeries.iteratedDeriv_alternating`), `D₀ = ∑ aₙ/n² ≥ a₁ = 1`.
* Taylor at 2 (`hasSum_taylorSeries_on_ball`, radius 2), `β ∈ [7/8,1)`, `x = 2 − β ∈ (1, 9/8]`:
  `G(β) = ∑ xⁿ cₙ`, `cₙ = Dₙ/n! − λ`, `|cₙ| ≤ M_G (2/3)ⁿ`. For every `M ≥ 1`:
  `Re G(β) ≥ 1 − Re λ (x^M − 1)/(x − 1) − M_G ∑_{n≥M} (2x/3)ⁿ`, with `2x/3 ≤ 3/4`.
  Since `Re F(β) = Re G(β) − Re λ/(x−1)`:
  `Re F(β) ≥ 1 − |λ| x^M/(1−β) − 16000 Q² (3/4)^M`.
* `M` minimal with `(4/3)^M ≥ 32000 Q²`: last term ≤ 1/2, `(4/3)^M ≤ 50000 Q²`;
  `x ≤ e^{1−β} ≤ (4/3)^{4(1−β)}` (`log(4/3) ≥ 1/4`), so `x^M ≤ (50000 Q²)^{4(1−β)}`.
* **Lemma A**: `Re F(β) ≤ 0`, `7/8 ≤ β < 1` ⇒ `|λ| ≥ (1−β)/2 · (50000 Q²)^{−4(1−β)}`.

## 5. Imprimitive/equivalent characters (`SiegelThm/Euler.lean`)
If `ψ = 1` then `changeLevel χ₂ = changeLevel χ₁` (level Q) and by `LFunction_changeLevel`
`L(1,χ₂) Π_{p|Q}(1−χ₂(p)/p) = L(1,χ₁) Π_{p|Q}(1−χ₁(p)/p)`, so
`|L(1,χ₂)| ≥ |L(1,χ₁)| (Π_{p|Q}(1−1/p))²` (using `(1+1/p)(1−1/p) ≤ 1`).
`Π_{p|n}(1−1/p) ≥ 2^{−P} n^{−η}` for `P ≥ 2^{1/η}`: `1−1/p ≥ p^{−η}` if `p ≥ P`, `≥ ½ p^{−η}`
otherwise; `Π_{p|n} p ≤ n`.

## 6. Siegel (`SiegelThm/Main.lean`)
`0 < ε ≤ 1` (wlog), `δ = ε/16`. Dichotomy:
(a) some real non-principal `χ₁` (any modulus) has `L(β₁,χ₁) = 0`, `β₁ ∈ [1−δ,1)`: `F(β₁) = 0`.
(b) otherwise: `χ₁ = χ₄`, `β₁ = 1−δ`. `P(t)` is real for real `t > 0` (integral formula with
real `A`), nonzero on `[1−δ, 2]` (hypothesis (b) + Mathlib non-vanishing on `Re ≥ 1`) and
`P(2) > 0` (`ζ(2)P(2) = ∑ aₙ/n² > 0`, `ζ(2) > 0`), so `P(β₁) > 0` (IVT);
`1/(β₁−1) + H(β₁) ≤ −16 + 1 < 0` ⇒ `F(β₁) < 0`.
In both cases, for `χ` mod `N`, `Q = N₁N`:
* `ψ ≠ 1`: Lemma A, `|L(1,ψ)| ≤ Q^{ε/2}·2/ε`, `1−β₁ ≤ δ`:
  `|L(1,χ)| ≥ (1−β₁)/2 · (50000N₁²)^{−ε/4} N^{−ε/2} / (|L(1,χ₁)| · 2/ε · N₁^{ε/2} N^{ε/2})`.
* `ψ = 1`: §5 with `η = ε/2`.
`c` = minimum of the two constants (depends on `ε, χ₁, β₁` only — ineffective, as it must be).
Non-primitive characters need no reduction: nothing above uses primitivity.

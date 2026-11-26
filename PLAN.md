# Plan: a complete, Palomar-ready Lean proof

Target statement: `tests/ChallengeDraft.lean`, theorem `harris_constant_attained`. On the unit ball of L^∞(𝕋),
sup |φ| = 2 and sup |q| = 8/(3√3), both attained, so ‖φ‖ = (3√3/4)‖q‖. It imports only Mathlib.

Palomar's constraints (see `palomar-registry.org/how-to-submit`):
- no `sorry` and **no `native_decide`**; only `propext`, `Classical.choice` and `Quot.sound`;
- the proof is replayed in Lean's kernel and in nanoda;
- every file starts with `module` and has ≤ 10,000 lines;
- Challenge/Solution split checked by comparator, plus `formalization.yaml`, a licence and a public GitHub repo at a fixed commit.

## Status (2026-11-26)

- **Done.** `Polarization.harris_constant_attained` (`Challenge.lean`, `Solution.lean`) is proved with only `propext`,
  `Classical.choice` and `Quot.sound`. All phases below are complete; see `README.md`.
- Left before submitting: review `formalization.yaml`, run `lake comparator` on Linux (it needs `bwrap`), and create the public repository and commit.

## Phases

1. **Kernel-checkable global certificate.**
   - Measured: with `decide +kernel` and ℚ arithmetic, one cut over 128 cells takes about 10 s. At that rate the
     current certificate (6456 cuts × 1024 cells) would need about 140 h.
   - Redesign:
     - one aggregated cut per leaf, γ* = Σ yᵢγᵢ (valid because N is a norm): 2349 N̄ checks instead of 6456;
     - Int fixed-point arithmetic for the per-cut work. Per cell, check S² ≥ Â·B̂ with S from a short Newton
       iteration; AM-GM with λ = s/A then gives ∫|P|w ≤ s;
     - about 256 cells, with the cell data checked once in ℚ;
     - the tree stored as nested Lean terms, with data split across files of ≤ 10k lines;
     - `decide +kernel` in parallel chunks.
   - Target: under 30 minutes of kernel time in total (nanoda will need about the same).
2. **From L^∞(𝕋) to the moment problem.**
   - a_k = `fourierCoeff`;
   - the support inequality Re Σ γ_k a_k ≤ N(γ), and |a_k| ≤ 1;
   - the rotation U_β and the reflection R on Fourier coefficients;
   - Lemma 10 (minimizing α, the normalization a₁ ≥ 0, invariance of the slabs);
   - ‖φ‖ = 2: Bessel's inequality and ‖B‖ = 2 for the upper bound, φ(e^{it}, e^{2it}) = 2 for the lower bound;
   - a(h₀) = (0, r, 2/3, −2r/3) from the Fourier series of 1/(z+r).
3. **The local theorem** (`harris_sharp.tex`, sections 3–6).
   - The basic identity and the second variation S as identity minus a finite-rank operator on L²(ρ).
   - Closed-form Gram integrals ∫ zⁿ/|P| dη and ∫ h₀² zⁿ/|P| dη, via Fourier series.
   - The spectral gap by an exact LDLᵀ in ℚ(√3), checked by the kernel.
   - The constants:
     - Λ₂ by polynomial-positivity certificates on the circle;
     - L₁₁⁻ (a supremum over 𝕋²), which needs a cheaper argument or a 2-D certificate;
     - c₂ in closed form.
   - Alignment (a minimizing α, and the vanishing derivative) and the final estimate.
   - Some slack is available: a cruder constant only shrinks X₀, and the global step still closes with X₀ halved.
4. **Packaging.**
   - `module` headers, `Challenge.lean` and `Solution.lean`, `comparator.json`, `formalization.yaml`
     (including AI-use disclosure) and a licence;
   - CI with comparator and nanoda;
   - a public repository, which is your decision.

Main risks: the L₁₁⁻ certificate, the Gram-matrix integrals in Lean, and the overall size (a rough estimate is
8–15k lines of Lean).

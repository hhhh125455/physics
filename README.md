# Classical Spin Krylov — Lean Verification

Lean 4 + Mathlib project for formal verification of algebraic steps in classical-spin Lanczos calculations.

## Scope

The initial proof module checks the consistency of the first two Lanczos coefficients with the second and fourth spectral moments. **It does not yet prove** the classical spin dynamics, the integral formula for the autocorrelation, Gegenbauer orthogonality, or the all-order Lanczos coefficients.

## Versions

Lean 4 and Mathlib are pinned to v4.32.0. GitHub Actions runs the Lean build automatically on each push and pull request.

## Build locally

```bash
lake update
lake exe cache get
lake build
```

## CI

See the Actions tab for the `Lean verification` workflow. A green build means the project typechecks, not that every physical assertion has been formalized.

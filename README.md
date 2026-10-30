# Classical Spin Krylov — Lean → Human-readable proofs

Lean 4 / Mathlib v4.32.0 project for progressively verifying the classical-spin Krylov calculation, with paired Chinese LaTeX derivations.

## Outputs

- [Detailed, step-by-step LaTeX](docs/detailed_zh.tex) — shows every essential calculation **of the verified moment-integral portion**, plus explicitly tagged unverified physical steps.
- [Concise paper-style LaTeX](docs/paper_zh.tex) — suitable as a draft for a physics paper.
- [Proof traceability map](docs/PROOF_MAP.md) — matches each important mathematical claim to its Lean theorem and human-language explanation.
- [Machine proofs](ClassicalSpinKrylov.lean) — theorems checked by Lean, not numerical sampling.

## What Lean checks now

It proves `∫_{-1}^{1} z^(2n) dz = 2/(2n+1)`, the weighted polynomial integral, and the full *even-moment formula* for all natural `n`. It also checks the low-order Lanczos/moment algebraic identities.

**It does not yet formalize** spin Poisson brackets, dynamics, the correlation trigonometric integral, the moment–Lanczos operator correspondence, or the all-order Lanczos coefficients. A green CI is not a proof of these missing parts.

## Reproduce

```sh
lake update
lake exe cache get
python3 scripts/check_traceability.py
lake build
```

GitHub Actions runs the same commands after each commit. A passing build confirms Lean accepted the stated theorems and the traceability checklist found the associated readable documentation; natural-language fidelity still requires review.

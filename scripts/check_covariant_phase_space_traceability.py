#!/usr/bin/env python3
"""Check that each covariant-phase-space proof-map symbol exists in Lean."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
proof_map = (root / "docs/COVARIANT_PHASE_SPACE_PROOF_MAP.md").read_text(encoding="utf-8")

modules = {
    "ClassicalSpinKrylov/CovariantPhaseSpaceAudit.lean": [
        "constraint_kernel_eq",
        "higherOrderMomentum_recursion",
        "higherOrderMomentum_eq_forward",
        "reverse_kernel_inclusion",
        "full_kernel_eq_from_bridge",
        "full_kernel_eq_from_quotient_cauchy_map_properties",
        "pairing_independent_of_lifts",
        "quotient_pairing_nondegenerate",
        "quotient_pairing_unique",
        "cartan_invariance_of_horizontal_closed_form",
        "closedness_descends",
        "sphere_scalar_curvature_injective",
        "two_sphere_scalar_curvature_injective",
        "invariant_observable_excludes_gauge",
    ],
    "ClassicalSpinKrylov/CovariantPhaseSpaceD3A.lean": [
        "iterated_integration_by_parts",
        "finite_order_variation_identity",
        "totalBoundary_eq_endpointMomentum_pairing",
    ],
    "ClassicalSpinKrylov/CovariantPhaseSpaceMomentum.lean": [
        "higherOrderEuler_eq_F0_sub_D_momentum",
    ],
    "ClassicalSpinKrylov/CovariantPhaseSpaceFactorization.lean": [
        "linearFunctional_factors_through_surjective",
        "constraint_kernel_eq_of_surjective",
    ],
}

for relative_path, symbols in modules.items():
    source = (root / relative_path).read_text(encoding="utf-8")
    for symbol in symbols:
        if not re.search(rf"\b(?:theorem|lemma)\s+{re.escape(symbol)}\b", source):
            raise SystemExit(f"Missing Lean declaration {symbol} in {relative_path}")
        if f"`{symbol}`" not in proof_map:
            raise SystemExit(f"Missing proof-map entry for {symbol}")

if "D1 | Not formalized" not in proof_map:
    raise SystemExit("The proof map must explicitly identify D1 as not formalized.")
if "algebraic dual" not in proof_map or "continuous dual" not in proof_map:
    raise SystemExit("The proof map must state the D2 dual-space boundary.")
if "Killing fields" not in proof_map or "conical singularities" not in proof_map:
    raise SystemExit("The proof map must state the GR linearization-stability caveat.")

print(f"Covariant phase-space traceability PASS: {sum(map(len, modules.values()))} declarations mapped; D1 and analytic boundaries explicit.")

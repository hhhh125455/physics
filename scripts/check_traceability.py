#!/usr/bin/env python3
"""Syntactic theorem↔document traceability, not semantic translation verification."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
moment_source = (root / "ClassicalSpinKrylov.lean").read_text(encoding="utf-8")
spin_source = (root / "ClassicalSpinKrylov/Dynamics.lean").read_text(encoding="utf-8")
moment_text = (root / "docs/detailed_zh.tex").read_text(encoding="utf-8")
spin_text = (root / "docs/dynamics_zh.tex").read_text(encoding="utf-8")
paper = (root / "docs/paper_zh.tex").read_text(encoding="utf-8")
mapping = (root / "docs/PROOF_MAP.md").read_text(encoding="utf-8")

moment_theorems = [
    "odd_power_neg_one", "even_power_integral", "spin_weight_integral",
    "evenMoment_formula", "moment_normalized", "moment_two", "moment_four",
    "fourth_moment_identity", "second_lanczos_identity",
]
spin_theorems = [
    "bracket_xy", "bracket_yz", "bracket_zx", "bracket_antisymm",
    "hamiltonian_z_derivative", "vectorField_x", "vectorField_y",
    "vectorField_z", "lengthSq_derivative_zero", "energy_derivative_zero",
    "evolve_zero", "evolve_z", "planar_rotation_length",
    "evolve_lengthSq", "evolve_hamiltonian",
]
for symbol in moment_theorems:
    if not re.search(rf"\b(?:private\s+)?theorem\s+{symbol}\b", moment_source):
        raise SystemExit(f"Missing Lean moment theorem: {symbol}")
    if f"\\LeanRef{{{symbol}}}" not in moment_text:
        raise SystemExit(f"Missing human derivation for moment theorem: {symbol}")
    if symbol not in mapping:
        raise SystemExit(f"Missing moment mapping: {symbol}")

for symbol in spin_theorems:
    if not re.search(rf"\b(?:private\s+)?theorem\s+{symbol}\b", spin_source):
        raise SystemExit(f"Missing Lean dynamics theorem: {symbol}")
    if symbol.replace("_", "\\_") not in spin_text:
        raise SystemExit(f"Missing human derivation for dynamics theorem: {symbol}")
    if symbol not in mapping:
        raise SystemExit(f"Missing dynamics mapping: {symbol}")

for term in ["尚未", "积分", "Lanczos"]:
    if term not in moment_text or term not in paper:
        raise SystemExit(f"Missing review-status marker: {term}")

print(f"Traceability PASS: {len(moment_theorems)} moments + "
      f"{len(spin_theorems)} dynamics theorems mapped to human-readable steps.")

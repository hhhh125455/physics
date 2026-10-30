#!/usr/bin/env python3
"""Basic traceability guard: detects missing theorem names and doc references.
This is NOT a semantic validator for human-language mathematical arguments.
"""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
lean = (root / "ClassicalSpinKrylov.lean").read_text(encoding="utf-8")
detailed = (root / "docs/detailed_zh.tex").read_text(encoding="utf-8")
paper = (root / "docs/paper_zh.tex").read_text(encoding="utf-8")
mapping = (root / "docs/PROOF_MAP.md").read_text(encoding="utf-8")

theorems = [
    "odd_power_neg_one",
    "even_power_integral",
    "spin_weight_integral",
    "evenMoment_formula",
    "moment_normalized",
    "moment_two",
    "moment_four",
    "fourth_moment_identity",
    "second_lanczos_identity",
]
for symbol in theorems:
    if not re.search(rf"\b(?:private\s+)?theorem\s+{symbol}\b", lean):
        raise SystemExit(f"Missing Lean theorem: {symbol}")
    if f"\\LeanRef{{{symbol}}}" not in detailed:
        raise SystemExit(f"Missing detailed proof reference: {symbol}")
    if f"\`{symbol}\`" not in mapping:
        raise SystemExit(f"Missing mapping entry: {symbol}")

for term in ["尚未", "积分", "Lanczos"]:
    if term not in detailed or term not in paper:
        raise SystemExit(f"Missing status marker: {term}")

for forbidden in ["sorry", "admit"]:
    if re.search(rf"\b{forbidden}\b", "\n".join(
        line for line in lean.splitlines()
        if line.lstrip().startswith(("theorem", "by", "  ", "def"))
    )):
        raise SystemExit(f"Unfinished proof placeholder: {forbidden}")

print("Traceability checks passed: 9 Lean theorems mapped to detailed derivation.")

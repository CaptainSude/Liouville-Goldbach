"""Check fresh output from Audit.lean using only the Python standard library."""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
if len(sys.argv) != 2:
    raise SystemExit("Usage: python check_axioms.py PATH_TO_FRESH_AUDIT_LOG")
log = Path(sys.argv[1]).read_text(encoding="utf-8-sig")
expected = set(re.findall(r"#print axioms ([\w.]+)", (root / "Audit.lean").read_text(encoding="utf-8")))
entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log)
if not expected or {name for name, _ in entries} != expected or len(entries) != len(expected):
    raise SystemExit("The axiom audit is incomplete or contains unexpected declarations.")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, raw in entries:
    axioms = {part.strip() for part in raw.split(",") if part.strip()}
    if not axioms <= allowed:
        raise SystemExit(f"Unapproved axioms for {name}: {sorted(axioms - allowed)}")
    if name == "LiouvilleGoldbach.liouville_goldbach" and axioms != allowed:
        raise SystemExit("The final theorem's axiom list differs from the verified result.")
print(f"Axiom audit passed for all {len(entries)} declarations, including the final theorem.")

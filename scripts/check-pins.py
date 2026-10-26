#!/usr/bin/env python3
"""Check the extraction binaries and Lake checkout revisions before regenerating Lean."""
import argparse
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lean-only", action="store_true",
                    help="Check Lean dependencies without checking extraction binaries")
args = parser.parse_args()

root = Path(__file__).resolve().parent.parent


def output(*args):
    return subprocess.check_output(args, cwd=root, text=True).strip()


def require(condition, message):
    if not condition:
        raise SystemExit(message)


require((root / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0",
        "Unexpected Lean toolchain")
manifest = json.loads((root / "lake-manifest.json").read_text())
expected = {
    "VCVio": "2567392aabfcf1c29a8a7958e4f750829952d83f",
    "aeneas": "da2b22e78d8fd5f076a902a5617c34038409fb79",
}
for package in manifest["packages"]:
    name, rev = package["name"], package["rev"]
    require(name not in expected or rev == expected[name], f"Unexpected {name} manifest pin")
    checkout = root / ".lake/packages" / name
    require(output("git", "-C", str(checkout), "rev-parse", "HEAD") == rev,
            f"{name} checkout does not match lake-manifest.json")
require(expected.keys() <= {p["name"] for p in manifest["packages"]},
        "Missing direct dependencies in manifest")
if args.lean_only:
    print("Lean dependency checkouts and pins agree.")
    raise SystemExit(0)

charon_pin = "".join(
    line.strip() for line in (root / ".lake/packages/aeneas/charon-pin").read_text().splitlines()
    if not line.startswith("#")
)
require(charon_pin == "4ad295c1bf982b5533ce7d85f4ddc889ff3127f8", "Extraction tools still target the previous backend; validate Lean separately with --lean-only")
require(output(str(root / ".tools/aeneas/charon"), "version") == f"0.1.245 ({charon_pin})",
        "Charon binary does not match the Lean backend's pin")
require(output(str(root / ".tools/aeneas/aeneas"), "-version") ==
        "aeneas nightly-2026.08.27-5b9dcf3", "Unexpected Aeneas binary")
print("Lean dependency checkouts and extraction binary pins agree.")

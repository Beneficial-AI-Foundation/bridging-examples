#!/usr/bin/env python3
"""Check the extraction binaries and Lake checkout revisions before regenerating Lean."""
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent


def output(*args):
    return subprocess.check_output(args, cwd=root, text=True).strip()


def require(condition, message):
    if not condition:
        raise SystemExit(message)


require((root / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.31.0",
        "Unexpected Lean toolchain")
manifest = json.loads((root / "lake-manifest.json").read_text())
expected = {
    "VCVio": "4bba755c0db64867c61e9a59f70dbe8fb8096ff9",
    "aeneas": "5b9dcf33dccdb1560ea7203ac57ea202476b6ed3",
}
for package in manifest["packages"]:
    name, rev = package["name"], package["rev"]
    require(name not in expected or rev == expected[name], f"Unexpected {name} manifest pin")
    checkout = root / ".lake/packages" / name
    require(output("git", "-C", str(checkout), "rev-parse", "HEAD") == rev,
            f"{name} checkout does not match lake-manifest.json")
require(expected.keys() <= {p["name"] for p in manifest["packages"]},
        "Missing direct dependencies in manifest")
charon_pin = "".join(
    line.strip() for line in (root / ".lake/packages/aeneas/charon-pin").read_text().splitlines()
    if not line.startswith("#")
)
require(charon_pin == "4ad295c1bf982b5533ce7d85f4ddc889ff3127f8", "Unexpected Charon pin")
require(output(str(root / ".tools/aeneas/charon"), "version") == f"0.1.245 ({charon_pin})",
        "Charon binary does not match the Lean backend's pin")
require(output(str(root / ".tools/aeneas/aeneas"), "-version") ==
        "aeneas nightly-2026.08.27-5b9dcf3", "Unexpected Aeneas binary")
print("Lean dependency checkouts and extraction binary pins agree.")

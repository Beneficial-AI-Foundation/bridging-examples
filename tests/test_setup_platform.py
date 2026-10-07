"""Exercise platform selection without downloading or running foreign binaries."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class SetupPlatformTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "scripts").mkdir()
        for name in ("setup-tools.sh", "env.sh"):
            shutil.copyfile(ROOT / "scripts" / name, self.root / "scripts" / name)
        self.bin = self.root / "bin"
        self.bin.mkdir()
        uname = self.bin / "uname"
        uname.write_text('#!/bin/sh\ncase "$1" in\n-s) echo "$TEST_OS";;\n-m) echo "$TEST_ARCH";;\nesac\n')
        uname.chmod(0o755)

    def run_setup(self, system, arch, *args):
        env = dict(os.environ, TEST_OS=system, TEST_ARCH=arch)
        env["PATH"] = str(self.bin) + os.pathsep + env["PATH"]
        return subprocess.run(
            ["bash", str(self.root / "scripts/setup-tools.sh"), *args],
            env=env, text=True, capture_output=True, check=False,
        )

    def test_supported_platforms_are_read_only(self):
        cases = [
            ("Linux", "x86_64", "linux-x86_64", "x86_64-unknown-linux-gnu"),
            ("Linux", "aarch64", "linux-aarch64", "aarch64-unknown-linux-gnu"),
            ("Linux", "arm64", "linux-aarch64", "aarch64-unknown-linux-gnu"),
            ("Darwin", "arm64", "macos-aarch64", "aarch64-apple-darwin"),
            ("Darwin", "aarch64", "macos-aarch64", "aarch64-apple-darwin"),
        ]
        for system, arch, asset, host in cases:
            with self.subTest(system=system, arch=arch):
                result = self.run_setup(system, arch, "--print-platform")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(f"asset=aeneas-{asset}.tar.gz", result.stdout)
                self.assertIn(f"rust_host={host}", result.stdout)
                self.assertFalse((self.root / ".tools").exists())

    def test_unsupported_platforms_fail_before_install(self):
        for system, arch in [("Darwin", "x86_64"), ("MINGW64_NT", "x86_64"),
                             ("Linux", "i686"), ("FreeBSD", "amd64")]:
            with self.subTest(system=system, arch=arch):
                result = self.run_setup(system, arch)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("No pinned extraction binary bundle", result.stderr)
                self.assertFalse((self.root / ".tools").exists())

    def test_corrupt_cached_archive_is_rejected(self):
        downloads = self.root / ".tools/downloads"
        downloads.mkdir(parents=True)
        (downloads / "aeneas-linux-x86_64.tar.gz").write_bytes(b"invalid archive")
        result = self.run_setup("Linux", "x86_64")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("SHA-256 mismatch", result.stderr)
        self.assertFalse((self.root / ".tools/aeneas/aeneas").exists())


if __name__ == "__main__":
    unittest.main()

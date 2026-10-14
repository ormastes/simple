#!/usr/bin/env python3
"""Exercise the production manifest ordering function without a compiler."""
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "bootstrap-phase-verification.shs"
SOURCE = SCRIPT.read_text()
FUNCTION = SOURCE.split("order_repository_test_manifest() {", 1)[1].split(
    "\nrun_repository_full_tests() {", 1
)[0]
FUNCTION = "order_repository_test_manifest() {" + FUNCTION


class RepositoryTestOrder(unittest.TestCase):
    def order(self, mode, paths):
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "manifest"
            manifest.write_text("".join(path + "\n" for path in paths))
            return subprocess.run(
                ["sh", "-c", FUNCTION + '\norder_repository_test_manifest "$1" "$2" "$3"',
                 "order-test", str(manifest), "/fixture with spaces", mode],
                capture_output=True, text=True, check=False,
            )

    def test_default_preserves_lexical_inventory_exactly(self):
        paths = ["/fixture with spaces/test/01_unit/app/a_spec.spl",
                 "/fixture with spaces/test/01_unit/compiler/z_spec.spl"]
        result = self.order("lexical", paths)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "".join(path + "\n" for path in paths))

    def test_simple_first_preserves_every_row_and_order_within_tiers(self):
        root = "/fixture with spaces/test/"
        core = [root + "01_unit/compiler/z_spec.spl", root + "01_unit/lib/a_spec.spl",
                root + "02_integration/language/b_test.spl", root + "03_system/runtime/c_spec.spl",
                root + "stdlib/d_spec.spl"]
        other = [root + "01_unit/app/compiler/a_spec.spl", root + "01_unit/tools/b_spec.spl",
                 root + "02_integration/app/runtime/c_spec.spl", root + "tools/compiler/d_spec.spl"]
        paths = sorted(core + other)
        result = self.order("simple-first", paths)
        self.assertEqual(result.returncode, 0, result.stderr)
        actual = result.stdout.splitlines()
        self.assertEqual(actual, sorted(core) + sorted(other))
        self.assertCountEqual(actual, paths)
        self.assertEqual(len(set(actual)), len(paths))

    def test_empty_inventory_stays_empty_and_invalid_order_refuses(self):
        self.assertEqual(self.order("simple-first", []).stdout, "")
        result = self.order("unknown", ["/fixture with spaces/test/compiler/a_spec.spl"])
        self.assertEqual(result.returncode, 2)
        self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()

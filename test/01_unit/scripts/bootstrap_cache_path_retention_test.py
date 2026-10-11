#!/usr/bin/env python3
"""Exercise the real diagnostic collector against canonical bootstrap cache names."""
import json
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]
COLLECTOR = ROOT / "scripts/bootstrap/collect-diagnostic-continuation.py"

class CachePathRetention(unittest.TestCase):
    def test_actual_bootstrap_names_and_owner_metadata(self):
        wanted = [
            "build/bootstrap/stage3/x/stage2-native-cache/scope-a/objects/a.o",
            "build/bootstrap/stage3/x/stage3-native-cache/scope-b/objects/b.obj",
            "build/bootstrap/stage3/x/stage2-native-cache/scope-a/.cache_scope",
            "build/bootstrap/stage3/x/stage2-native-cache/scope-a/incremental_manifest.txt",
        ]
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory) / "repo"
            root.mkdir()
            for name in wanted + ["build/bootstrap/not-native-cache/ignore.o", "elsewhere/native_cache/ignore.o"]:
                item = root / name
                item.parent.mkdir(parents=True, exist_ok=True)
                item.write_bytes(b"fixture")
            output = pathlib.Path(directory) / "collected"
            result = subprocess.run(["python3", str(COLLECTOR), str(root), str(output), "4096"], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = json.loads((output / "receipt.json").read_text())
            self.assertEqual({row["path"] for row in receipt["files"]}, set(wanted))
            self.assertEqual(receipt["admission"], "UNADMITTED")
            self.assertEqual(receipt["preserved_bytes"], 4 * len(b"fixture"))
            for name in wanted:
                self.assertEqual((output / "files" / name).read_bytes(), b"fixture")

if __name__ == "__main__":
    unittest.main()

"""Fail-closed CI dependency admission tests; never emulate a Simple compiler."""
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile


ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("prepare_mail_config_helper", ROOT / "scripts/ci/prepare_mail_config_helper.py")
prepare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prepare)


class AdmissionTests(unittest.TestCase):
    def test_missing_platform_producer_fails_instead_of_using_a_seed(self):
        with patch.dict("os.environ", {"MAIL_CI_PHASE2_PRODUCERS_JSON": "{}"}):
            with self.assertRaisesRegex(SystemExit, "no existing producer is configured"):
                prepare.main()

    def test_wrong_generation_is_rejected_before_download(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(prepare.urllib.request, "urlopen") as download:
            with self.assertRaisesRegex(SystemExit, "must declare phase 2"):
                prepare.provision({"phase": 1}, Path(directory))
            download.assert_not_called()

    def test_corrupted_bundle_never_reaches_extraction_or_execution(self):
        entry = {"phase": 2, "sha256": "0" * 64, "url": "https://example.invalid/pinned-producer", "format": "zip"}
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(prepare.urllib.request, "urlopen", return_value=io.BytesIO(b"corrupt bundle")):
                with self.assertRaisesRegex(SystemExit, "checksum does not match"):
                    prepare.provision(entry, Path(directory))
            self.assertFalse((Path(directory) / "producer").exists())

    def test_zip_path_traversal_is_refused_after_checksum_validation(self):
        payload = io.BytesIO()
        with zipfile.ZipFile(payload, "w") as archive:
            archive.writestr("../../escaped-compiler", "not executable")
        data = payload.getvalue()
        entry = {"phase": 2, "sha256": hashlib.sha256(data).hexdigest(), "url": "https://example.invalid/pinned-producer", "format": "zip"}
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(prepare.urllib.request, "urlopen", return_value=io.BytesIO(data)):
                with self.assertRaisesRegex(SystemExit, "escapes its staging directory"):
                    prepare.provision(entry, Path(directory))


if __name__ == "__main__":
    unittest.main()

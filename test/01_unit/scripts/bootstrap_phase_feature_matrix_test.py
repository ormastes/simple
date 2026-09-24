"""Controller contracts only; fixture launches never count as phase evidence."""

import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location(
    "phase_feature_matrix",
    ROOT / "scripts/check/check-bootstrap-phase-feature-matrix.py",
)
MATRIX = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MATRIX)


class PhaseFeatureMatrixContract(unittest.TestCase):
    def write_artifact(self, root, name, executable, generation, compiler_sha=None):
        artifact_path = Path(executable).resolve()
        artifact_sha = MATRIX.digest(artifact_path)
        provenance = root / (name + ".provenance.txt")
        provenance.write_text("fixture provenance for " + name + "\n", encoding="utf-8")
        provenance_sha = MATRIX.digest(provenance)
        admission = root / (name + ".admission.json")
        admission.write_text(json.dumps({
            "schema": "BootstrapPhaseFeatureAdmissionV1",
            "phase": 2,
            "generation": generation,
            "status": "ADMITTED",
            "artifact_path": str(artifact_path),
            "artifact_sha256": artifact_sha,
            "compiler_sha256": compiler_sha or artifact_sha,
            "provenance_sha256": provenance_sha,
            "capability_set_sha256": MATRIX.canonical_digest(["native-build", "test"]),
        }), encoding="utf-8")
        return {
            "path": str(artifact_path),
            "sha256": artifact_sha,
            "generation": generation,
            "provenance": {"path": str(provenance.resolve()), "sha256": provenance_sha},
            "admission": {"path": str(admission.resolve()), "sha256": MATRIX.digest(admission)},
        }

    def manifest(self, root):
        generation = "phase2-fixture-generation"
        compiler = self.write_artifact(root, "compiler", sys.executable, generation)
        return {
            "schema": "BootstrapPhaseFeatureManifestV1",
            "phase": 2,
            "generation": generation,
            "bootstrap_jobs": {"selected": 3, "detected_cpu_count": 8},
            "capability_set": ["native-build", "test"],
            "compiler": compiler,
            "artifacts": {},
            "rows": {},
        }

    def pin(self, artifact):
        return {
            "artifact_sha256": artifact["sha256"],
            "generation": artifact["generation"],
            "provenance_sha256": artifact["provenance"]["sha256"],
            "admission_sha256": artifact["admission"]["sha256"],
        }

    def test_fixed_rows_pair_each_major_family_in_both_modes(self):
        for family in (
            "compiler", "language_runtime", "simple_mcp", "simple_lsp_mcp",
            "t32_mcp", "spipe_sspec", "caret", "slang", "simd_db_web", "devhub",
        ):
            self.assertIn(family + "_interpreter", MATRIX.ROWS)
            self.assertIn(family + "_native", MATRIX.ROWS)
        for row in (
            "simple_mcp_protocol", "simple_lsp_mcp_protocol", "t32_mcp_protocol",
            "spipe_plugin_launch", "caret_protocol", "slang_binary_launch",
            "devhub_launch", "devhub_github", "devhub_jira", "devhub_confluence",
        ):
            self.assertIn(row, MATRIX.ROWS)

    def test_explicit_bootstrap_oversubscription_is_evidence_not_staleness(self):
        with tempfile.TemporaryDirectory() as folder:
            manifest = self.manifest(Path(folder))
            manifest["bootstrap_jobs"] = {"selected": 12, "detected_cpu_count": 8}
            MATRIX.validate_manifest(manifest)

    def test_stale_generation_is_rejected_before_launch(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            manifest = self.manifest(root)
            manifest["compiler"]["generation"] = "older-phase2-generation"
            with self.assertRaises(MATRIX.Verdict) as result:
                MATRIX.admitted_artifact(manifest, "compiler")
            self.assertEqual(result.exception.reason, "stale-artifact-generation:compiler")

    def test_phase1_compiler_must_match_current_generation_pointer(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            target = root / "target"
            generation = "phase1-current-fixture"
            generation_dir = target / "bootstrap.generations" / generation
            generation_dir.mkdir(parents=True)
            seed = generation_dir / "simple"
            seed.write_bytes(b"current phase1 seed fixture")
            seed_sha = MATRIX.digest(seed)
            inputs = "a" * 64
            stamp = generation_dir / "simple.inputs.sha256"
            stamp.write_text(
                "schema=simple-bootstrap-seed-artifact-stamp-v2\n"
                + "inputs_fingerprint=" + inputs + "\n"
                + "seed_sha256=" + seed_sha + "\n",
                encoding="utf-8",
            )
            marker = target / "bootstrap.current.env"
            marker.write_text(
                "schema=simple-bootstrap-authority-current-v1\n"
                + "generation=" + generation + "\n"
                + "inputs_fingerprint=" + inputs + "\n"
                + "generation_sha256=" + "b" * 64 + "\n"
                + "stamp_sha256=" + MATRIX.digest(stamp) + "\n",
                encoding="utf-8",
            )
            manifest = {
                "schema": "BootstrapPhaseFeatureManifestV1",
                "phase": 1,
                "generation": generation,
                "bootstrap_jobs": {"selected": 8, "detected_cpu_count": 8},
                "capability_set": ["native-build"],
                "compiler": {"path": str(seed.resolve()), "sha256": seed_sha},
                "rows": {},
                "current_authority": {
                    "path": str(marker.resolve()), "sha256": MATRIX.digest(marker),
                },
            }
            handoff = root / "phase1-handoff.json"
            handoff.write_text(json.dumps({
                "schema": "simple-bootstrap-phase1-current-handoff-v1",
                "status": "current-committed",
                "artifact_path": str(seed.resolve()),
                "artifact_sha256": seed_sha,
                "admission_path": str(marker.resolve()),
                "admission_sha256": MATRIX.digest(marker),
                "generation": generation,
                "selected_jobs": 8,
                "detected_available_cpus": 8,
                "stamp_path": str(stamp.resolve()),
                "stamp_sha256": MATRIX.digest(stamp),
            }), encoding="utf-8")
            manifest["handoff"] = {
                "path": str(handoff.resolve()), "sha256": MATRIX.digest(handoff),
            }
            authority = MATRIX.validate_current_phase_authority(manifest)
            self.assertEqual(authority["admitted_compiler_sha256"], seed_sha)
            exact_handoff = MATRIX.validate_phase1_handoff(manifest)
            self.assertEqual(exact_handoff["stamp_path"], str(stamp.resolve()))
            marker.write_text(marker.read_text().replace(generation, "older-phase1"), encoding="utf-8")
            manifest["current_authority"]["sha256"] = MATRIX.digest(marker)
            with self.assertRaises(MATRIX.Verdict) as result:
                MATRIX.validate_current_phase_authority(manifest)
            self.assertEqual(result.exception.reason, "phase1-current-generation-mismatch")

    def test_stale_row_sha_pin_is_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            manifest = self.manifest(root)
            artifact = MATRIX.admitted_artifact(manifest, "compiler")
            row = self.pin(manifest["compiler"])
            row["artifact_sha256"] = "0" * 64
            with self.assertRaises(MATRIX.Verdict) as result:
                MATRIX.validate_row_pin(row, artifact)
            self.assertEqual(result.exception.reason, "stale-row-artifact-pin:artifact_sha256")

    def test_relative_or_script_tool_cannot_be_launched(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            relative = {"path": "simple", "sha256": "0" * 64}
            with self.assertRaises(MATRIX.Verdict) as result:
                MATRIX.bound_file(relative, native=True)
            self.assertEqual(result.exception.reason, "artifact-path-not-absolute")
            script = root / "old-simple.cmd"
            script.write_text("@exit /b 0\n", encoding="utf-8")
            with self.assertRaises(MATRIX.Verdict) as result:
                MATRIX.bound_file({"path": str(script.resolve()), "sha256": MATRIX.digest(script)}, native=True)
            self.assertEqual(result.exception.reason, "native-executable-required")

    def test_provider_help_words_cannot_hide_implementation_failure(self):
        row = {"blocked_output": ["login", "token", "request failed"]}
        output = "Usage: devhub auth login --token TOKEN\nfatal implementation crash\n"
        with self.assertRaises(MATRIX.Verdict) as result:
            MATRIX.check_output("devhub_github", row, 1, output)
        self.assertEqual(result.exception.status, "FAIL")
        self.assertEqual(result.exception.reason, "process-nonzero-exit")

    def test_anchored_auth_failure_is_blocked_only_for_provider_rows(self):
        output = "You are not logged into any GitHub hosts.\n"
        with self.assertRaises(MATRIX.Verdict) as provider:
            MATRIX.check_output("devhub_github", {}, 1, output)
        self.assertEqual(provider.exception.status, "BLOCKED")
        with self.assertRaises(MATRIX.Verdict) as ordinary:
            MATRIX.check_output("devhub_launch", {}, 1, output)
        self.assertEqual(ordinary.exception.status, "FAIL")

    def test_crash_cannot_be_downgraded_by_unauthorized_output(self):
        for code in (-11, 139):
            with self.subTest(code=code):
                with self.assertRaises(MATRIX.Verdict) as result:
                    MATRIX.check_output("devhub_github", {}, code, "HTTP 401\n")
                self.assertEqual(result.exception.status, "FAIL")
                self.assertEqual(result.exception.reason, "process-crashed")

    def test_absent_rows_fail_and_retain_resume_and_job_evidence(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            manifest = self.manifest(root)
            manifest_path = root / "manifest.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            output = root / "receipts"
            result = MATRIX.main(["--manifest", str(manifest_path), "--output", str(output)])
            self.assertEqual(result, 1)
            receipts = [json.loads((output / (row + ".json")).read_text()) for row in MATRIX.ROWS]
            self.assertTrue(all(item["status"] == "FAIL" for item in receipts))
            self.assertTrue(all(not item["launched"] and item["resume_argv"] for item in receipts))
            self.assertTrue(all(item["selected_bootstrap_jobs"] == 3 for item in receipts))
            self.assertTrue(all(item["detected_cpu_count"] == 8 for item in receipts))
            self.assertTrue(all(item["release_evidence"] is False for item in receipts))

    def test_declared_unsupported_row_does_not_launch(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            manifest = self.manifest(root)
            manifest["rows"]["t32_mcp_native"] = {
                "support": "unsupported",
                "reason": "phase2-t32-native-artifact-not-admitted",
                "owner": "phase2-owner",
                "reviewer": "phase2-reviewer",
                "prerequisite": "admit the Phase 2 T32 native artifact",
            }
            manifest_path = root / "manifest.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            output = root / "receipts"
            output.mkdir()
            receipt = MATRIX.run_row(
                manifest, manifest_path, MATRIX.digest(manifest_path), output, 5,
                "t32_mcp_native", Path(MATRIX.__file__).resolve(),
            )
            self.assertEqual(receipt["status"], "UNSUPPORTED")
            self.assertFalse(receipt["launched"])
            self.assertEqual(receipt["compiler_sha256"], manifest["compiler"]["sha256"])
            self.assertEqual(receipt["owner"], "phase2-owner")
            self.assertTrue(receipt["resume_argv"])

    def test_successful_fixture_uses_exact_absolute_admitted_executable(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            manifest = self.manifest(root)
            compiler_sha = manifest["compiler"]["sha256"]
            tool = self.write_artifact(
                root, "plugin-runtime", sys.executable,
                manifest["generation"], compiler_sha=compiler_sha,
            )
            plugin_entry = root / "spipe-plugin-entry.txt"
            plugin_entry.write_text("installed plugin fixture\n", encoding="utf-8")
            manifest["artifacts"]["plugin_runtime"] = tool
            row = {
                "support": "supported",
                "kind": "command",
                "artifact": "plugin_runtime",
                "owner": "fixture-owner",
                "reviewer": "fixture-reviewer",
                "args": ["-c", "print('self-review plugin ready')", str(plugin_entry.resolve())],
                "expected_stdout": ["self-review plugin ready"],
                "inputs": [{"path": str(plugin_entry.resolve()), "sha256": MATRIX.digest(plugin_entry)}],
            }
            row.update(self.pin(tool))
            manifest["rows"]["spipe_plugin_launch"] = row
            manifest_path = root / "manifest.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            output = root / "receipts"
            output.mkdir()
            receipt = MATRIX.run_row(
                manifest, manifest_path, MATRIX.digest(manifest_path), output, 5,
                "spipe_plugin_launch", Path(MATRIX.__file__).resolve(),
            )
            self.assertEqual(receipt["status"], "PASS", receipt)
            self.assertTrue(receipt["launched"])
            self.assertEqual(receipt["executable_path"], str(Path(sys.executable).resolve()))
            self.assertEqual(receipt["executable_sha256"], MATRIX.digest(sys.executable))
            self.assertEqual(receipt["generation"], manifest["generation"])
            self.assertEqual(receipt["selected_bootstrap_jobs"], 3)
            self.assertEqual(receipt["detected_cpu_count"], 8)
            self.assertFalse(receipt["release_evidence"])


if __name__ == "__main__":
    unittest.main()

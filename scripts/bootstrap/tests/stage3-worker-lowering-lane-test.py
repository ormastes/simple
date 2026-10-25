"""Check real Stage 3 lane argument/recipe transport without a compiler.

Only the worker prefix and final recipe are executed. Admission, resource
enforcement and the compiler are outside this test; the transcript function
records a NUL-separated vector instead of launching anything.
"""
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[3]
WORKER = (ROOT / "scripts/bootstrap/lib/stage3-native-build-worker.sh").read_text()
RESUME = (ROOT / "scripts/bootstrap/resume-stage3-from-admitted.sh").read_text()
PREFIX = WORKER[:WORKER.index('BOOTSTRAP_STAGE3_FACADE_PATH=')]
RECIPE = WORKER[WORKER.index('bootstrap_stage3_run_transcribed "$transcript"'):]
LANE = RESUME[RESUME.index('stage3_lowering_lane=per-file'):RESUME.index('stage3_cold_init_env=')]
DIGEST_START = RESUME.index('stage3_args=$(bootstrap_stage3_args_sha256')
DIGEST_END = RESUME.index('src/app/cli/bootstrap_main.spl)', DIGEST_START)
DIGEST = RESUME[DIGEST_START:DIGEST_END + len('src/app/cli/bootstrap_main.spl)')]


def worker_args(count=32, lane="per-file"):
    args = ["/fixture/transcript", "/fixture/root", "/fixture/log",
            "/fixture/home", "/fixture/tmp", "/usr/bin:/bin",
            "/fixture/admitted", "aarch64-apple-darwin", "llvm", "10", "600",
            "/fixture/cache with space", "/fixture/runtime", "/fixture/candidate",
            "/fixture/progress", "/fixture/phase", "/fixture/memory", "fixture-id",
            "native", "none", "4194304", "", "", "", "4096", "v1",
            "/fixture/admission", "a" * 64]
    if count >= 30:
        args += ["", ""]
    if count >= 31:
        args += ["1000"]
    if count == 32:
        args += [lane]
    return args


class WorkerLoweringLane(unittest.TestCase):
    def record(self, script, args=(), whole_program=None):
        with tempfile.TemporaryDirectory(prefix="stage3-lane-vector-") as tmp:
            record = Path(tmp) / "vector"
            env = {"PATH": os.defpath, "CONTROL_RECORD": str(record)}
            if whole_program is not None:
                env["SIMPLE_BOOTSTRAP_WHOLE_PROGRAM"] = whole_program
            result = subprocess.run(["sh", "-c", script, "lane-test", *args],
                                    env=env, capture_output=True, timeout=10)
            vector = record.read_bytes().split(b"\0")[:-1] if record.exists() else None
            return result, vector

    def worker(self, count=32, lane="per-file", whole_program=None):
        recorder = 'bootstrap_stage3_run_transcribed() { shift 6; printf "%s\\0" "$@" >"$CONTROL_RECORD"; };\n'
        timeout = 'timeout_args=\n[ -z "$timeout_seconds" ] || timeout_args="--timeout $timeout_seconds"\n'
        return self.record(PREFIX + recorder + timeout + RECIPE,
                           worker_args(count, lane), whole_program)

    def test_legacy_vectors_remain_identical(self):
        vectors = []
        for count in (28, 30, 31):
            with self.subTest(count=count):
                result, vector = self.worker(count, whole_program="1")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(vector.count(b"SIMPLE_BOOTSTRAP=1"), 1)
                self.assertFalse(any(v.startswith(b"SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=") for v in vector))
                vectors.append(vector)
        self.assertEqual(vectors[0], vectors[1])
        self.assertEqual(vectors[1], vectors[2])

    def test_explicit_lanes_reach_actual_recipe(self):
        for lane, flag, whole in (("per-file", b"SIMPLE_BOOTSTRAP=", False),
                                 ("whole-program", b"SIMPLE_BOOTSTRAP=1", True)):
            with self.subTest(lane=lane):
                result, vector = self.worker(lane=lane, whole_program="1")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual([v for v in vector if v.startswith(b"SIMPLE_BOOTSTRAP=")], [flag])
                self.assertEqual(vector.count(b"SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1"), int(whole))
                separator = vector.index(b"--")
                self.assertEqual(vector[separator + 1:separator + 3],
                                 [b"/fixture/admitted", b"native-build"])
                self.assertIn(b"/fixture/cache with space", vector)

    def test_invalid_lane_refuses_before_recording(self):
        for lane in ("", "invalid", "per-file whole-program"):
            with self.subTest(lane=lane):
                result, vector = self.worker(lane=lane)
                self.assertEqual(result.returncode, 64, result.stderr)
                self.assertIn(b"invalid lowering lane", result.stderr)
                self.assertIsNone(vector)

    def test_resume_hash_vector_equals_worker_vector_for_both_lanes(self):
        args = worker_args()
        values = dict(zip(("transcript", "root", "log", "home", "tmp", "path", "admitted",
                           "platform", "stage2_backend", "stage3_threads", "timeout_seconds",
                           "stage3_cache", "runtime", "candidate", "progress", "phase_profile",
                           "memory_snapshot", "evidence_run_id", "stage3_requested_route",
                           "stage3_fallback_route"), args[:20]))
        values.update(stage3_mc_env="", stage3_cold_init_env="", stage3_diagnostic_env="",
                      stage3_compiler_ceiling_env="", resume_abi_policy="v1",
                      stage2_admission="/fixture/admission", stage3_timeout_args="--timeout 600")
        # Fail if a newly added recipe input was not deliberately bound here.
        variables = set(re.findall(r"\$(?:\{)?([A-Za-z_][A-Za-z_0-9]*)", DIGEST))
        self.assertFalse(variables - values.keys() - {"stage3_bootstrap_flag", "stage3_whole_program_env",
                                                             "stage3_per_file_env"})
        assignments = "\n".join(f"{key}={shlex.quote(value)}" for key, value in values.items())
        recorder = 'bootstrap_stage3_args_sha256() { printf "%s\\0" "$@" >"$CONTROL_RECORD"; };\n'
        for lane, whole in (("per-file", None), ("whole-program", "1")):
            with self.subTest(lane=lane):
                result, expected = self.record("set -eu\n" + assignments + "\n" + LANE + recorder + DIGEST, whole_program=whole)
                self.assertEqual(result.returncode, 0, result.stderr)
                worker_result, actual = self.worker(lane=lane)
                self.assertEqual(worker_result.returncode, 0, worker_result.stderr)
                separator = actual.index(b"--")
                self.assertEqual(expected, actual[:separator] + actual[separator + 2:])


if __name__ == "__main__":
    unittest.main()

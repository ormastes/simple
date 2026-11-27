#!/usr/bin/env python3
"""Process-level selector contracts; not compiler/BuildRunner qualification."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "run-build.shs"


class SelectorTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="build selector ")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.program = self.root / "owner with spaces"
        self.program.write_text(
            "#!/usr/bin/env python3\nimport json,os,sys\n"
            "print(json.dumps({'args':sys.argv[1:],'pid':os.getpid(),"
            "'cwd':os.getcwd()}))\nsys.exit(int(os.environ.get('TEST_EXIT','0')))\n"
        )
        self.program.chmod(0o700)

    def invoke(self, *args, **env):
        base = dict(os.environ)
        base.pop("SIMPLE_BUILD_EXECUTOR", None)
        base.update(env)
        child = subprocess.Popen(
            ["sh", str(SCRIPT), f"--program={self.program}", *args],
            cwd=self.root, env=base, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True,
        )
        out, err = child.communicate(timeout=10)
        return child.returncode, out, err, child.pid

    def test_buildrunner_owns_run(self):
        code, out, err, _ = self.invoke(
            "--executor=buildrunner", "--", "--manifest", "manifest with spaces",
            "--state", "state", "--source-root", "source",
        )
        self.assertEqual(code, 0, err)
        self.assertEqual(json.loads(out)["args"],
                         ["run", "--manifest", "manifest with spaces", "--state",
                          "state", "--source-root", "source"])

    def test_direct_default_exact_argv_and_exec(self):
        args = ["--source", "source with spaces", "--backend", "llvm", "--output", "out;$(x)"]
        code, out, err, pid = self.invoke("--", *args)
        self.assertEqual(code, 0, err)
        observed = json.loads(out)
        self.assertEqual(observed["args"], ["native-build", *args])
        self.assertEqual(observed["pid"], pid)
        self.assertEqual(observed["cwd"], str(self.root))

    def test_config_and_cli_precedence(self):
        code, out, err, _ = self.invoke("--", "--manifest", "m", SIMPLE_BUILD_EXECUTOR="buildrunner")
        self.assertEqual(code, 0, err)
        self.assertEqual(json.loads(out)["args"][0], "run")
        code, out, err, _ = self.invoke("--executor=direct", "--", "input.spl", SIMPLE_BUILD_EXECUTOR="invalid")
        self.assertEqual(code, 0, err)
        self.assertEqual(json.loads(out)["args"], ["native-build", "input.spl"])

    def test_exact_failure_propagates(self):
        for mode in ["direct", "buildrunner"]:
            with self.subTest(mode=mode):
                code, _, _, _ = self.invoke(f"--executor={mode}", "--", "input", TEST_EXIT="37")
                self.assertEqual(code, 37)

    def test_invalid_selector_never_starts_owner(self):
        for options in [("--executor=test-runner", "--", "x"),
                        ("--executor=", "--", "x"), ("--bogus",),
                        ("--executor=direct",), ("--",),
                        ("--executor=direct", "--executor=buildrunner", "--", "x")]:
            with self.subTest(options=options):
                code, out, err, _ = self.invoke(*options)
                self.assertEqual(code, 2)
                self.assertEqual(out, "")
                self.assertIn("run-build:", err)

    def test_invalid_config_rejected(self):
        code, out, _, _ = self.invoke("--", "x", SIMPLE_BUILD_EXECUTOR="invalid")
        self.assertEqual(code, 2)
        self.assertEqual(out, "")

    def test_help_requires_no_compiler(self):
        result = subprocess.run(["sh", str(SCRIPT), "--help"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0)
        for word in ["direct", "buildrunner", "SIMPLE_BUILD_EXECUTOR", "TestRunner"]:
            self.assertIn(word, result.stdout)

    def test_missing_program_rejected(self):
        for args in [["--", "x"], ["--program=/no/such/compiler", "--", "x"]]:
            result = subprocess.run(["sh", str(SCRIPT), *args], capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("run-build:", result.stderr)


if __name__ == "__main__":
    unittest.main()

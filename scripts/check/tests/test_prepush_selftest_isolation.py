"""Run the real recursion checker against disposable caller repositories."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[3]
CHECKER = Path("scripts/check/check-prepush-no-recursion.shs")
DISPATCHER = Path("scripts/hooks/pre-push")
SH = shutil.which("sh") or "C:/Program Files/Git/bin/sh.exe"


class PrepushSelftestIsolation(unittest.TestCase):
    def check_caller(self, inherited):
        with tempfile.TemporaryDirectory(prefix="prepush-caller-") as tmp:
            caller = Path(tmp)
            env = os.environ.copy()
            local_vars = subprocess.check_output(
                ["git", "rev-parse", "--local-env-vars"], cwd=ROOT, text=True
            ).splitlines()
            for key in local_vars:
                env.pop(key, None)

            def git(*args):
                return subprocess.check_output(
                    ["git", *args], cwd=caller, env=env, stderr=subprocess.STDOUT
                )

            git("init", "-q")
            git("config", "user.name", "Fixture")
            git("config", "user.email", "fixture@example.invalid")
            git("config", "core.autocrlf", "false")
            for relative in (CHECKER, DISPATCHER):
                target = caller / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((ROOT / relative).read_bytes())
            git("add", ".")
            git("-c", "core.hooksPath=/dev/null", "commit", "-qm", "caller")
            (caller / "staged").write_text("staged caller content\n")
            git("add", "staged")
            (caller / "untracked").write_text("untracked caller content\n")

            def snapshot():
                files = {str(p.relative_to(caller)): p.read_bytes()
                         for p in caller.rglob("*")
                         if p.is_file() and ".git" not in p.relative_to(caller).parts}
                return (git("rev-parse", "HEAD"),
                        (caller / ".git/index").read_bytes(),
                        (caller / ".git/config").read_bytes(),
                        git("status", "--porcelain"), files)

            # Refresh status before taking the exact-byte index snapshot.
            git("status", "--porcelain")
            before = snapshot()
            child_env = env.copy()
            if inherited:
                for key, suffix in {
                    "GIT_DIR": ".git", "GIT_WORK_TREE": ".",
                    "GIT_INDEX_FILE": ".git/index", "GIT_COMMON_DIR": ".git",
                    "GIT_OBJECT_DIRECTORY": ".git/objects",
                }.items():
                    child_env[key] = (caller / suffix).resolve().as_posix()
            run = subprocess.run([SH, CHECKER.as_posix()], cwd=caller,
                                 env=child_env, capture_output=True, text=True,
                                 timeout=100)
            after = snapshot()
            labels = ("HEAD", "index", "config", "status", "files")
            changed = [label for label, a, b in zip(labels, before, after) if a != b]
            self.assertEqual(changed, [], f"caller mutated: {changed}; {run.stdout} {run.stderr}")
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertIn("PASS", run.stdout)
            self.assertIn("3 fixture(s) checked", run.stdout)

    def test_normal_environment(self):
        self.check_caller(False)

    def test_inherited_repository_environment(self):
        self.check_caller(True)


if __name__ == "__main__":
    unittest.main()

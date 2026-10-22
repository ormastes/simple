"""Compare independently expanded Stage 3 hash and execution recipes.

The shell functions are replaced by argument collectors; no compiler is run.
"""
import itertools
from pathlib import Path
import re
import shlex
import subprocess
import unittest


ROOT = Path(__file__).resolve().parents[3]


class Stage3InvocationConsistency(unittest.TestCase):
    def test_stage2_layout_accepts_current_root_and_bound_legacy_donor(self):
        source = (ROOT / "scripts/check/lib/bootstrap-stage3/manifest-verify.shs").read_text()
        start = source.index('    bootstrap_stage3_stage2_suffix="')
        end = source.index('    [ "$(bootstrap_stage3_verify_value stage2_path', start)
        recipe = source[start:end]
        for platform in ("x86_64-unknown-linux-gnu", "x86_64-pc-windows-msvc"):
            suffix = ".exe" if "windows" in platform else ""
            for output, accepted in (("/fixture/build", True), ("/fixture/donor/output", True), ("/fixture/unrelated", False)):
                with self.subTest(platform=platform, output=output):
                    script = (
                        f"bootstrap_stage3_platform={shlex.quote(platform)}\n"
                        "bootstrap_stage3_manifest_output_root=/fixture/build\n"
                        f"bootstrap_stage3_expected_stage2_path={shlex.quote(output + '/stage2/' + platform + '/simple' + suffix)}\n"
                        "bootstrap_stage3_normalized_absolute() { case \"$1\" in /*) return 0;; *) return 1;; esac; }\n"
                        "bootstrap_stage3_provenance_fail() { return 1; }\n"
                        "verify_layout() {\n" + recipe + '\nprintf "%s\\n" "$bootstrap_stage3_stage2_output_display";\n}\nverify_layout'
                    )
                    result = subprocess.run(["sh", "-c", script], cwd=ROOT, text=True, capture_output=True, timeout=10)
                    self.assertEqual(result.returncode == 0, accepted)
                    if accepted:
                        self.assertEqual(result.stdout.strip(), output)

    def test_hash_binds_the_executed_environment_and_arguments(self):
        source = (ROOT / "scripts/bootstrap/bootstrap-from-scratch.sh").read_text()
        hash_start = source.index("  stage3_build_args_sha256=$(")
        hash_end = source.index("\n  )", hash_start) + len("\n  )")
        hash_recipe = source[hash_start:hash_end]
        stage3 = source.index("  # Stage 3:")
        run_start = source.index("  bootstrap_stage3_run_transcribed \\", stage3)
        run_end = source.index("\n  stage3_status=$?", run_start)
        run_recipe = source[run_start:run_end]
        names = set(re.findall(r"\$\{?([A-Za-z_][A-Za-z_0-9]*)", hash_recipe + run_recipe))
        for windows, low_memory in itertools.product((False, True), repeat=2):
            with self.subTest(windows=windows, low_memory=low_memory):
                values = {name: f"fixture-{name}" for name in names}
                values.update(
                    NATIVE_LOW_MEMORY="1" if low_memory else "0",
                    k1_composition_source_args="--source /fixture/k1",
                    stage3_mc_env="SIMPLE_SAFETY_PROFILE=critical SIMPLE_ASSURANCE_WARNING_PHASE=1",
                    stage3_diagnostic_env="SIMPLE_HIR_TRACE=1",
                    bootstrap_windows_abi_env="SIMPLE_WINDOWS_ABI=msvc SIMPLE_LINKER_FLAVOR=msvc" if windows else "",
                    bootstrap_windows_cc_env="CC=fixture clang-cl" if windows else "",
                    bootstrap_windows_include_env="INCLUDE=fixture include" if windows else "",
                    bootstrap_windows_lib_env="LIB=fixture lib" if windows else "",
                    bootstrap_windows_libpath_env="LIBPATH=fixture libpath" if windows else "",
                )
                assignments = "\n".join(f"{name}={shlex.quote(value)}" for name, value in sorted(values.items()))
                common = assignments + "\nabsolute_path() { printf '%s\\n' \"$1\"; }\n"
                expected = subprocess.run(
                    ["sh", "-c", common + "bootstrap_stage3_args_sha256() { printf '%s\\n' \"$@\"; }\n" + hash_recipe + '\nprintf "%s\\n" "$stage3_build_args_sha256"'],
                    cwd=ROOT, text=True, capture_output=True, timeout=10, check=True,
                ).stdout.splitlines()
                actual = subprocess.run(
                    ["sh", "-c", common + "bootstrap_stage3_run_transcribed() { shift 6; printf '%s\\n' \"$@\"; }\n" + run_recipe],
                    cwd=ROOT, text=True, capture_output=True, timeout=10, check=True,
                ).stdout.splitlines()
                separator = actual.index("--")
                self.assertEqual(actual[separator + 1], values["stage2_admitted_absolute"])
                # The argument hash excludes the executable and its -- separator.
                actual = actual[:separator] + actual[separator + 2:]
                self.assertEqual(expected, actual)


if __name__ == "__main__":
    unittest.main()

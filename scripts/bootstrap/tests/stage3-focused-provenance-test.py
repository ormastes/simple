"""Exercise focused Stage 2/3 provenance reconstruction without a compiler."""

import os
from pathlib import Path
import re
import shlex
import subprocess
import unittest
import uuid


ROOT = Path(__file__).resolve().parents[3]
BOOTSTRAP = ROOT / "scripts/bootstrap/bootstrap-from-scratch.sh"
AUTHORITY = "scripts/check/lib/bootstrap-stage3/authority.shs"
VERIFY = "scripts/check/lib/bootstrap-stage3/manifest-verify.shs"
SNAPSHOT = "scripts/check/lib/bootstrap-stage3/command-snapshot.shs"


def shell_quote(value):
    return shlex.quote(str(value))


def extract_assignment(source, name):
    start = source.index(f"  {name}=$(\n")
    end = source.index("\n  )", start) + len("\n  )")
    return source[start:end]


class FocusedProvenance(unittest.TestCase):
    def setUp(self):
        self.source = BOOTSTRAP.read_text(encoding="utf-8")
        self.recipes = {
            "stage2": extract_assignment(self.source, "stage2_build_args_sha256"),
            "stage3": extract_assignment(self.source, "stage3_build_args_sha256"),
        }
        self.helper_sources = f'. "{AUTHORITY}"\n. "{SNAPSHOT}"\n. "{VERIFY}"\n'

    def fixture_values(self, platform, low_memory, diagnostics, cold_init, mission_critical):
        names = set(re.findall(r"\$\{?([A-Za-z_][A-Za-z_0-9]*)", "\n".join(self.recipes.values())))
        values = {name: f"fixture-{name}" for name in names}
        output = "/tmp/focused-stage2-output"
        current = "/tmp/focused-current-output"
        provenance = f"{current}/stage3/{platform}"
        stage2_cache = f"{output}/stage3/{platform}/stage2-native-cache"
        stage3_cache = f"{provenance}/stage3-native-cache"
        runtime = f"{provenance}/stage2-runtime-authority"
        suffix = ".exe" if "windows" in platform else ""
        values.update(
            PLATFORM=platform,
            platform=platform,
            backend="llvm",
            bootstrap_mode="release",
            simple_abi_policy="v1",
            SIMPLE_PLUGIN_MANIFEST_POLICY="simple-sdn",
            SIMPLE_KERNEL_K1_POLICY="llvm-cranelift",
            SIMPLE_COVERAGE_CUTOVER_STATE="atomic-apk-only",
            k1_composition_sha256_before="a" * 64,
            NATIVE_LOW_MEMORY="1" if low_memory else "0",
            stage_build_rust_log="error",
            stage_build_path="/fixture/toolchain/bin:/usr/bin",
            bootstrap_link_library_path="/fixture/link-compat",
            bootstrap_link_compat_sha256="a" * 64,
            k1_composition_source_args="--source src/compositions/kernel_llvm_cranelift",
            cuda_source_root=str(ROOT).replace("\\", "/") + "/src/compositions/cuda_disabled",
            plugin_policy_source_root=str(ROOT).replace("\\", "/") + "/src/plugins",
            compiler_ceiling_env="",
            stage2_preflight_context_env="",
            stage2_diagnostic_env="",
            cuda_composition_root="/tmp/focused-current-output/compositions/cuda-" + "b" * 64 + "-" + "c" * 64,
            stage2_bin=f"{output}/stage2/{platform}/simple{suffix}",
            stage3_bin=f"{current}/stage3/{platform}/simple{suffix}",
            stage2_seed_absolute=f"{runtime}/simple{suffix}",
            stage2_admitted_absolute=f"{output}/stage3/{platform}/stage2-admitted/simple{suffix}",
            stage2_cache_absolute=stage2_cache,
            stage3_cache_absolute=stage3_cache,
            stage_runtime_absolute=runtime,
            stage2_compatibility_manifest_absolute=f"{output}/stage3/{platform}/phase2-compatibility.manifest",
            stage2_provenance_dir=f"{output}/stage3/{platform}",
            stage3_provenance_dir=provenance,
            stage2_compatibility_manifest=f"{output}/stage3/{platform}/phase2-compatibility.manifest",
            build_progress_events=f"{current}/bootstrap-build-progress.events",
            stage2_build_progress_events=f"{output}/bootstrap-build-progress.events",
            stage3_phase_profile=f"{provenance}/phase-profile-v1.events",
            stage3_memory_snapshot=f"{provenance}/memory-snapshot-v1.events",
            stage3_evidence_run_id="stage3-fixture-run",
            jobs="3",
            selfhost_jobs="2",
            native_verbose_arg="--verbose",
            stage2_timeout_args="--timeout 900",
            stage2_cold_init_env="SIMPLE_SCV_INVENTORY_COLD_INIT=1" if cold_init else "",
            stage3_diagnostic_env=(
                "SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1" if diagnostics else ""
            ),
            SIMPLE_BOOTSTRAP_DIAG="1" if diagnostics else "",
            SIMPLE_COMPILER_TRACE="1" if diagnostics else "",
            SIMPLE_MIR_TAG_PROBE="1" if diagnostics else "",
            SIMPLE_KEEP_SOURCE_CONTENTS="",
            stage3_mc_env=(
                "SIMPLE_SAFETY_PROFILE=critical SIMPLE_ASSURANCE_WARNING_PHASE=1"
                if mission_critical else ""
            ),
            bootstrap_stage3_manifest_output_root=current,
            bootstrap_stage3_manifest_dir=provenance,
            bootstrap_stage3_stage2_output_display=output,
            bootstrap_stage3_root=str(ROOT),
            bootstrap_stage3_platform=platform,
            bootstrap_stage3_backend="llvm",
            bootstrap_stage3_mode="release",
            bootstrap_stage3_rust_log="error",
            bsfc_policy="llvm-cranelift",
            stage2_output_display=output,
            stage3_output_display=f"{current}/stage3/{platform}/simple.exe" if "windows" in platform else f"{current}/stage3/{platform}/simple",
            stage2_admission_receipt_absolute=f"{output}/stage3/{platform}/stage2-admitted/admission.env",
        )
        if "apple-darwin" in platform:
            values.update(
                bootstrap_stage2_darwin_env=1,
                CC="/opt/toolchain/bin/clang",
                CXX="/opt/toolchain/bin/clang++",
                AR="/opt/toolchain/bin/llvm-ar",
                LD="/opt/toolchain/bin/ld.lld",
                LLVM_CONFIG="/opt/toolchain/bin/llvm-config",
                SIMPLE_LLVM_REQUIRED_VERSION="23.1.1",
            )
        else:
            values["bootstrap_stage2_darwin_env"] = ""
        if "windows" in platform:
            values.update(
                bootstrap_windows_abi_env="SIMPLE_WINDOWS_ABI=msvc SIMPLE_LINKER_FLAVOR=msvc",
                bootstrap_windows_cc_env="CC=clang-cl.exe",
                bootstrap_windows_include_env="INCLUDE=C:/fixture/include",
                bootstrap_windows_lib_env="LIB=C:/fixture/lib",
                bootstrap_windows_libpath_env="LIBPATH=C:/fixture/libpath",
            )
        else:
            for name in (
                "bootstrap_windows_abi_env",
                "bootstrap_windows_cc_env",
                "bootstrap_windows_include_env",
                "bootstrap_windows_lib_env",
                "bootstrap_windows_libpath_env",
            ):
                values[name] = ""
        return values

    def assignments(self, values):
        lines = ["ROOT=$(pwd -P)"]
        for name, value in sorted(values.items()):
            if name in ("ROOT", "bootstrap_stage3_root", "PATH", "HOME", "TMPDIR", "IFS", "PWD", "SHLVL", "EUID", "UID"):
                continue
            if name == "k1_composition_source_args":
                lines.append(f'{name}="--source src/compositions/kernel_llvm_cranelift"')
            elif name in ("cuda_source_root", "plugin_policy_source_root"):
                suffix = "src/compositions/cuda_disabled" if name == "cuda_source_root" else "src/plugins"
                lines.append(f'{name}="$ROOT/{suffix}"')
            else:
                lines.append(f"{name}={shell_quote(value)}")
        lines.extend(
            [
                'bootstrap_stage3_root="$ROOT"',
                'bootstrap_stage3_args_sha256() { for value do printf \'%s:%s\\n\' "${#value}" "$value"; done; }',
            ]
        )
        return "\n".join(lines) + "\n"

    def producer_vector(self, phase, values):
        assignment = "stage2_build_args_sha256" if phase == "stage2" else "stage3_build_args_sha256"
        recipe = self.recipes[phase]
        script = self.assignments(values) + recipe + f'\nprintf "%s\\n" "${assignment}"\n'
        result = subprocess.run(
            ["sh"], cwd=ROOT, input=script, text=True, capture_output=True, timeout=45
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        return self.decode_vector(result.stdout)

    def decode_vector(self, output):
        values = []
        for record in output.rstrip("\n").split("\n"):
            length, value = record.split(":", 1)
            self.assertEqual(int(length), len(value), record)
            values.append(value)
        return values

    def focused_common(self, phase, values, transcript, vector):
        env_end = next(index for index, value in enumerate(vector) if value == "native-build")
        explicit_env = vector[:env_end]
        argv = vector[env_end:]
        executable = values["stage2_seed_absolute"] if phase == "stage2" else values["stage2_admitted_absolute"]
        writer_args = [
            transcript,
            "$ROOT",
            "$ROOT",
            values["stage_build_path"],
            *explicit_env,
            "--",
            executable,
            *argv,
        ]
        transcript_writer = (
            "bootstrap_stage3_write_command_transcript "
            + shell_quote(writer_args[0])
            + ' "$ROOT" "$ROOT" "$ROOT" '
            + " ".join(shell_quote(arg) for arg in writer_args[3:])
            + " || exit 90"
        )
        setup = self.assignments(values)
        setup += f"bootstrap_stage3_manifest=/tmp/focused-manifest.env\n"
        setup += f"bootstrap_stage3_stage2_output_display={shell_quote(values['stage2_output_display'])}\n"
        setup += f"bsfc_policy=llvm-cranelift\n"
        setup += "bsfc_cuda_mode=disabled\n"
        setup += f"bsfc_k1=\"$ROOT/src/compositions/kernel_llvm_cranelift\"\n"
        setup += f"bsfc_cuda={shell_quote(values['cuda_composition_root'])}\n"
        setup += "bootstrap_stage3_verify_value() { case \"$1\" in focused_low_memory) printf '%s\\n' \"${FIXTURE_LOW:-0}\" ;; focused_stage2_verbose) printf '%s\\n' 1 ;; focused_stage2_timeout) printf '%s\\n' 900 ;; focused_mission_critical) printf '%s\\n' \"${FIXTURE_MC:-0}\" ;; focused_k1_sha256) printf '%s\\n' " + "'" + "a" * 64 + "'" + " ;; stage2_threads) printf '%s\\n' 3 ;; stage3_threads) printf '%s\\n' 2 ;; *) return 1 ;; esac; }\n"
        setup += "bootstrap_stage3_map_value() { case \"$1\" in stage2_command_transcript_authority) printf '%s\\n' \"$FIXTURE_STAGE2_TRANSCRIPT\" ;; stage3_command_transcript_authority) printf '%s\\n' \"$FIXTURE_STAGE3_TRANSCRIPT\" ;; stage2_native_cache_dir_display) printf '%s\\n' \"$FIXTURE_STAGE2_CACHE\" ;; stage3_native_cache_dir_display) printf '%s\\n' \"$FIXTURE_STAGE3_CACHE\" ;; runtime_path_display) printf '%s\\n' \"$FIXTURE_RUNTIME\" ;; stage2_admission_receipt_display) printf '%s\\n' \"$FIXTURE_ADMISSION\" ;; seed_display) printf '%s\\n' \"$FIXTURE_SEED\" ;; stage2_admitted_display) printf '%s\\n' \"$FIXTURE_STAGE2_ADMITTED\" ;; stage2_display) printf '%s\\n' \"$FIXTURE_STAGE2_BIN\" ;; stage3_display) printf '%s\\n' \"$FIXTURE_STAGE3_BIN\" ;; *) return 1 ;; esac; }\n"
        setup += (
            f"FIXTURE_LOW={1 if '--low-memory' in vector else 0}\n"
            f"FIXTURE_MC={1 if 'SIMPLE_SAFETY_PROFILE=critical' in vector else 0}\n"
            f"FIXTURE_STAGE2_TRANSCRIPT={shell_quote(transcript if phase == 'stage2' else '/tmp/stage2-transcript')}\n"
            f"FIXTURE_STAGE3_TRANSCRIPT={shell_quote(transcript if phase == 'stage3' else '/tmp/stage3-transcript')}\n"
            f"FIXTURE_STAGE2_CACHE={shell_quote(values['stage2_cache_absolute'])}\n"
            f"FIXTURE_STAGE3_CACHE={shell_quote(values['stage3_cache_absolute'])}\n"
            f"FIXTURE_RUNTIME={shell_quote(values['stage_runtime_absolute'])}\n"
            f"FIXTURE_ADMISSION={shell_quote(values['stage2_admission_receipt_absolute'])}\n"
            f"FIXTURE_SEED={shell_quote(values['stage2_seed_absolute'])}\n"
            f"FIXTURE_STAGE2_ADMITTED={shell_quote(values['stage2_admitted_absolute'])}\n"
            f"FIXTURE_STAGE2_OUTPUT={shell_quote(values['stage2_output_display'])}\n"
            f"FIXTURE_STAGE2_BIN={shell_quote(values['stage2_bin'])}\n"
            f"FIXTURE_STAGE3_BIN={shell_quote(values['stage3_bin'])}\n"
            f"FIXTURE_PLATFORM={shell_quote(values['bootstrap_stage3_platform'])}\n"
        )
        setup += transcript_writer + "\n"
        return setup

    def test_focused_hash_and_transcript_match_producer_recipes(self):
        scenarios = (
            ("x86_64-unknown-linux-gnu", False, False, False, False),
            ("x86_64-pc-windows-msvc", True, True, True, True),
            ("aarch64-apple-darwin", False, False, False, False),
        )
        selected_cases = {
            case.strip()
            for case in os.environ.get("FOCUSED_PROVENANCE_CASES", "").split(",")
            if case.strip()
        }
        valid_cases = {
            f"{platform}:{phase}"
            for platform, *_ in scenarios
            for phase in ("stage2", "stage3")
        }
        self.assertLessEqual(
            selected_cases,
            valid_cases,
            f"unknown focused provenance case(s): {sorted(selected_cases - valid_cases)}",
        )
        for platform, low_memory, diagnostics, cold_init, mission_critical in scenarios:
            for phase in ("stage2", "stage3"):
                if selected_cases and f"{platform}:{phase}" not in selected_cases:
                    continue
                with self.subTest(platform=platform, phase=phase):
                    values = self.fixture_values(platform, low_memory, diagnostics, cold_init, mission_critical)
                    vector = self.producer_vector(phase, values)
                    # Concurrent bootstrap lanes must not replace each other's
                    # transcript between its hash and byte-comparison checks.
                    transcript = f"/tmp/focused-{phase}-{platform}-{uuid.uuid4().hex}.transcript"
                    setup = self.focused_common(phase, values, transcript, vector)
                    # Hash action returns the exact argument vector passed to the shared hasher.
                    expected = setup + f"bootstrap_stage3_focused_command hash {phase}\n"
                    result = subprocess.run(
                        ["sh"],
                        cwd=ROOT,
                        input=self.helper_sources + expected,
                        text=True,
                        capture_output=True,
                        timeout=45,
                    )
                    self.assertEqual(result.returncode, 0, result.stderr)
                    actual = self.decode_vector(result.stdout)
                    if actual != vector:
                        mismatch = [
                            (index, expected, actual[index] if index < len(actual) else "<missing>")
                            for index, expected in enumerate(vector)
                            if index >= len(actual) or actual[index] != expected
                        ][:8]
                        self.fail(
                            f"{phase} focused hash differs: expected={len(vector)} actual={len(actual)}; "
                            f"first mismatches={mismatch}"
                        )

                    # The transcript is written as length-prefixed records, then parsed
                    # by the production host/env/argv reader during the focused check.
                    check = setup + f"bootstrap_stage3_focused_command transcript {phase}\n"
                    result = subprocess.run(
                        ["sh"],
                        cwd=ROOT,
                        input=self.helper_sources + check,
                        text=True,
                        capture_output=True,
                        timeout=60,
                    )
                    self.assertEqual(result.returncode, 0, result.stderr[-2500:])


if __name__ == "__main__":
    unittest.main()

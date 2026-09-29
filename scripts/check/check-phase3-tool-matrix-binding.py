#!/usr/bin/env python3
"""Exercise real Phase3 matrix rejection gates; no admitted compiler is fabricated.

The inert host executable is only a startup fixture. Positive Phase3 execution
requires a real canonical manifest and remains a separate bootstrap criterion.
"""
import argparse
from contextlib import nullcontext
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile


def check_target_c_contracts(root, base, shell, counterpart_only=False):
    """Exercise input binding with disposable bytes, without admitting a compiler."""
    matrix = (root / "scripts/bootstrap/bootstrap-phase-verification.shs").read_text()
    helpers = matrix[matrix.index("snapshot_target_c_inputs() ("):
                     matrix.index("validate_phase_c_tool_binding() (")]
    fixture = base / "target-c-helper-fixture"
    runtime = fixture / "src/runtime"
    runtime.mkdir(parents=True)
    (runtime / "probe.c").write_text("int fixture(void) { return 1; }\n")
    (runtime / "probe.h").write_text("int fixture(void);\n")
    sdk_header = fixture / "tools/counterpart/sdk/c/simple_counterpart_abi.h"
    sdk_header.parent.mkdir(parents=True)
    sdk_header.write_text("#define FIXTURE_ABI 1\n")
    tools = base / "target-c-helper-tools"
    tools.mkdir()
    for name in ("clang", "clang++", "other-clang"):
        tool = tools / name
        tool.write_text("#!/bin/sh\nprintf 'clang version fixture-only\\n'\n")
        tool.chmod(0o755)
    helper_file = base / "target-c-extracted-functions.sh"
    helper_file.write_text(helpers, encoding="utf-8")
    script = base / "target-c-contracts.sh"
    script.write_text(r'''#!/bin/sh
set -eu
root=$1 fixture=$2 tools=$3 helpers=$4 evidence=$5 mode=$6
. "$root/scripts/bootstrap/bootstrap-phase-toolchain.shs"
. "$root/scripts/check/lib/bootstrap-stage3/authority.shs"
hash_file() { bootstrap_stage3_hash_file "$1"; }
hash_stream() { bootstrap_stage3_hash_stream; }
manifest_value() { sed -n "s/^$1=//p" "$2" | head -n 1; }
manifest_key_count() { awk -F= -v key="$1" '$1 == key {n++} END {print n+0}' "$2"; }
. "$helpers"
source_root=$fixture
target_c_platform=x86_64-unknown-linux-gnu
target_c_source_sha=$(printf 'selector fixture' | hash_stream)
CC=$tools/clang CXX=$tools/clang++
export CC CXX
snapshot_target_c_inputs "$evidence/original.env"
original=$(hash_file "$evidence/original.env")
printf '// changed SDK header\n' >>"$fixture/tools/counterpart/sdk/c/simple_counterpart_abi.h"
snapshot_target_c_inputs "$evidence/sdk.env"
[ "$(hash_file "$evidence/sdk.env")" != "$original" ]
[ "$(manifest_value target_counterpart_sdk_header_sha256 "$evidence/sdk.env")" != "$(manifest_value target_counterpart_sdk_header_sha256 "$evidence/original.env")" ]
printf 'PASS changed counterpart SDK header changes target identity\n'
[ "$mode" != counterpart-only ] || exit 0
original=$(hash_file "$evidence/sdk.env")
printf '// changed header\n' >>"$fixture/src/runtime/probe.h"
snapshot_target_c_inputs "$evidence/header.env"
[ "$(hash_file "$evidence/header.env")" != "$original" ]
printf 'PASS changed C header changes target identity\n'
printf '// changed source\n' >>"$fixture/src/runtime/probe.c"
snapshot_target_c_inputs "$evidence/source.env"
[ "$(hash_file "$evidence/source.env")" != "$(hash_file "$evidence/header.env")" ]
printf 'PASS changed C source changes target identity\n'
printf '# changed executable bytes\n' >>"$tools/clang"
snapshot_target_c_inputs "$evidence/tool.env"
[ "$(manifest_value target_c_tool_sha256 "$evidence/tool.env")" != "$(manifest_value target_c_tool_sha256 "$evidence/source.env")" ]
printf 'PASS changed C executable bytes change identity\n'
target_c_platform=aarch64-unknown-linux-gnu
snapshot_target_c_inputs "$evidence/target.env"
[ "$(hash_file "$evidence/target.env")" != "$(hash_file "$evidence/tool.env")" ]
printf 'PASS changed target changes profile identity\n'
phase=stage2
target_c_binding=$evidence/sdk.env
target_c_identity=$original
tool_input_identity=$(printf 'fixture producer' | hash_stream)
write_target_c_receipt_fields >"$evidence/owner-fields.env"
validate_target_c_receipt "$evidence/owner-fields.env"
sed 's/target_runtime_abi_policy=v1/target_runtime_abi_policy=v2/' "$evidence/owner-fields.env" >"$evidence/changed-owner.env"
if validate_target_c_receipt "$evidence/changed-owner.env"; then exit 1; fi
printf 'PASS changed target receipt field is rejected\n'
SIMPLE_NATIVE_RUNTIME_BUNDLE=bootstrap-tools
if prepare_phase_c_tool_binding; then exit 1; fi
unset SIMPLE_NATIVE_RUNTIME_BUNDLE
SIMPLE_ABI_POLICY=v2
if prepare_phase_c_tool_binding; then exit 1; fi
unset SIMPLE_ABI_POLICY
printf 'PASS conflicting profile and ABI are rejected\n'
capture_fixture() {
    [ "$SIMPLE_CC" = "$CC" ] && [ "$SIMPLE_PROJECT_ROOT" = "$source_root" ]
}
bootstrap_phase_run_command capture_fixture /bin/true native-build fixture.spl
printf 'PASS wrapper exports exact SIMPLE_CC and source root\n'
SIMPLE_CC=$tools/other-clang
if bootstrap_phase_run_command capture_fixture /bin/true native-build fixture.spl; then exit 1; fi
unset SIMPLE_CC
SIMPLE_PROJECT_ROOT=$tools
if bootstrap_phase_run_command capture_fixture /bin/true native-build fixture.spl; then exit 1; fi
printf 'PASS conflicting compiler and source root are rejected\n'
''', encoding="utf-8")
    evidence = base / "target-c-contract-evidence"
    evidence.mkdir()
    result = subprocess.run([shell, str(script), str(root), str(fixture),
                             str(tools), str(helper_file), str(evidence),
                             "counterpart-only" if counterpart_only else "all"],
                            text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=90)
    (base / "target-c-contracts.log").write_text(result.stdout, encoding="utf-8")
    expected = 1 if counterpart_only else 9
    if result.returncode or result.stdout.count("PASS ") != expected:
        raise AssertionError(f"target C helper contracts failed: {result.returncode}\n{result.stdout}")
    print(f"PASS {expected} target C helper contracts; fixture bytes were never compiled or admitted")


def check_windows_toolchain(root, base, shell):
    """Probe the real pinned C driver's version and executor environment only."""
    script = base / "windows-c-toolchain-contracts.sh"
    script.write_text(r'''#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$1" && pwd -P)
. "$root/scripts/bootstrap/bootstrap-windows-cl-mode.shs"
. "$root/scripts/bootstrap/bootstrap-phase-toolchain.shs"
case "$(uname -s)" in MINGW*|MSYS*|CYGWIN*) ;; *) exit 1 ;; esac
source_root=$root
MSYSTEM=MINGW64
export MSYSTEM
SIMPLE_NATIVE_BUILD_TARGET=$(bootstrap_phase_c_target_platform)
[ "$SIMPLE_NATIVE_BUILD_TARGET" = x86_64-pc-windows-msvc ]
export SIMPLE_NATIVE_BUILD_TARGET
printf 'PASS GNU MSYSTEM resolves to the executor MSVC target\n'
selected_cc=$(bootstrap_phase_c_compiler_path)
unset SIMPLE_CC
probe_executor() {
    if [ "$1" = "$selected_cc" ]; then "$@"; return; fi
    [ "$SIMPLE_CC" = "$selected_cc" ]
    [ "$SIMPLE_WINDOWS_ABI:$SIMPLE_LINKER_FLAVOR:$CL" = msvc:msvc:/TC ]
    [ "$SIMPLE_NATIVE_BUILD_TARGET" = x86_64-pc-windows-msvc ]
    [ "$(cygpath -u "$SIMPLE_PROJECT_ROOT")" = "$source_root" ]
}
bootstrap_phase_run_command probe_executor fixture-command native-build fixture.spl
printf 'PASS real pinned Windows driver and native root are exported\n'
SIMPLE_CC="$LLVM_SYS_231_PREFIX/bin/clang.exe"
if bootstrap_phase_run_command probe_executor fixture-command native-build fixture.spl; then exit 1; fi
unset SIMPLE_CC
SIMPLE_WINDOWS_ABI=gnu
if bootstrap_phase_run_command probe_executor fixture-command native-build fixture.spl; then exit 1; fi
printf 'PASS conflicting Windows driver and GNU ABI are rejected\n'
''', encoding="utf-8")
    result = subprocess.run([shell, str(script), str(root)], text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=90)
    (base / "windows-c-toolchain-contracts.log").write_text(result.stdout, encoding="utf-8")
    if result.returncode or result.stdout.count("PASS ") != 3:
        raise AssertionError(f"Windows toolchain contracts failed: {result.returncode}\n{result.stdout}")
    print("PASS 3 Windows C toolchain contracts; version probe only, no build or admission")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    parser.add_argument("--shell", default="bash")
    parser.add_argument("--fixture-executable", type=Path, default=Path("/bin/true"))
    parser.add_argument("--counterpart-header-only", action="store_true")
    parser.add_argument("--windows-toolchain-only", action="store_true")
    args = parser.parse_args()
    root = args.source_root.resolve()
    args.work_root.mkdir(parents=True, exist_ok=True)
    script = root / "scripts/bootstrap/bootstrap-phase-verification.shs"
    # Retain every diagnostic, including a failed fixture, under the chosen root.
    with nullcontext(tempfile.mkdtemp(prefix="phase3-binding-", dir=args.work_root)) as temp:
        base = Path(temp)
        if args.windows_toolchain_only:
            check_windows_toolchain(root, base, args.shell)
            return
        if args.counterpart_header_only:
            check_target_c_contracts(root, base, args.shell, counterpart_only=True)
            return
        compiler = args.fixture_executable.resolve(strict=True)
        digest = hashlib.sha256(compiler.read_bytes()).hexdigest()
        invalid = base / "invalid-provenance.env"
        invalid.write_text("schema=not-stage3-admission\n", encoding="utf-8")
        linked = base / "linked-provenance.env"
        try:
            linked.symlink_to(invalid)
        except OSError as error:
            raise RuntimeError("This rejection harness requires file-symlink creation; use WSL or enable the native host capability. No gate was skipped.") from error
        cases = [
            ("missing-provenance", ["--phase=stage3"], "Stage3 requires admitted provenance"),
            ("wrong-phase", ["--phase=stage2", f"--stage3-provenance={invalid}"], "stage3-only"),
            ("temporary-hash", ["--phase=stage3", f"--stage3-provenance={invalid}", "--hash-policy=temporary"], "canonical provenance"),
            ("missing-file", ["--phase=stage3", f"--stage3-provenance={base / 'missing.env'}"], "invalid Stage3 provenance file"),
            ("symlink-file", ["--phase=stage3", f"--stage3-provenance={linked}"], "invalid Stage3 provenance file"),
            ("invalid-authority", ["--phase=stage3", f"--stage3-provenance={invalid}"], "Stage3 provenance is not current"),
        ]
        for name, options, diagnostic in cases:
            work = base / name
            command = [args.shell, str(script), f"--compiler={compiler}",
                       f"--compiler-sha256={digest}", f"--source-root={root}",
                       f"--work-root={work}", *options]
            env = dict(os.environ, TMPDIR=str(base), SIMPLE_NO_BOOTSTRAP_DELEGATE="1",
                       SIMPLE_NO_STUB_FALLBACK="1", BOOTSTRAP_STAGE2_TEST_DELEGATE="0")
            result = subprocess.run(command, cwd=root, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=90)
            (base / f"{name}.log").write_text(result.stdout, encoding="utf-8")
            if result.returncode != 2 or diagnostic not in result.stdout:
                raise AssertionError(f"{name}: unexpected exit/diagnostic: {result.returncode}\n{result.stdout}")
            if list(work.glob("outputs/**/command-owners.*.env")):
                raise AssertionError(f"{name}: rejected authority published command owners")
            print(f"PASS {name}: rejected before command-owner publication")
        check_target_c_contracts(root, base, args.shell)
    print("PASS 6 rejection gates; positive admitted Phase3 execution remains pending")


if __name__ == "__main__":
    main()

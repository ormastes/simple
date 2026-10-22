#!/usr/bin/env python3
"""Exercise real Stage2 vectors, hermetic shell transport and recorded identities."""
import hashlib
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
LIB = ROOT / "scripts/check/lib/bootstrap-stage3"
SOURCE = (ROOT / "scripts/bootstrap/bootstrap-from-scratch.sh").read_text()
COMMAND = (LIB / "command-snapshot.shs").read_text()
RESUME = (ROOT / "scripts/bootstrap/resume-stage3-from-admitted.sh").read_text()
REPLAY = (ROOT / "scripts/bootstrap/resume-stage2-from-cache.sh").read_text()
DIAGNOSTICS = ("SIMPLE_MEM_SNAPSHOT_FILE", "SIMPLE_EVIDENCE_RUN_ID", "SIMPLE_M4_WORK_RECEIPT")
PREFIX = f". {shlex.quote(str(LIB / 'authority.shs'))}\n. {shlex.quote(str(LIB / 'command-snapshot.shs'))}\n"
ENV = {k: v for k, v in os.environ.items() if not k.startswith("SIMPLE_")}


def sections(source):
    start = source.index("  stage2_cold_init_env=\n")
    control = source[start:source.index("  stage3_evidence_run_id=", start)]
    start = source.index("  bootstrap_run_stage2_native() {")
    return control, source[start:source.index("\n  set +e", start)]


def shell(code):
    return subprocess.run(["sh", "-c", PREFIX + code], env=ENV,
                          capture_output=True, check=False)


def setup(values):
    return "\n".join(f"{k}={shlex.quote(v)}" for k, v in values.items()) + "\n"


def digest(vector):
    return hashlib.sha256(b"".join(str(len(x)).encode() + b":" + x + b"\n" for x in vector)).hexdigest()


def quoted(vector):
    return " ".join(shlex.quote(x.decode() if isinstance(x, bytes) else x) for x in vector)


control, runner = sections(SOURCE)
# Independent legacy vector from reviewed owner 809f4d449e959564143148071b47542acb90bf46,
# scripts/bootstrap/bootstrap-from-scratch.sh:3914-3969, for the controlled
# Linux/Cranelift/one-thread/low-memory scenario below. Keep literal values and
# argument boundaries: deriving this oracle from current source or Git HEAD would
# make a post-commit comparison vacuous and require history in shallow CI.
LEGACY_ENV = [item.encode() for item in """SIMPLE_LLVM_BIN=
SIMPLE_LLVM_PATH=
MIMALLOC_EAGER_COMMIT=0
MIMALLOC_ARENA_EAGER_COMMIT=0
MIMALLOC_PURGE_DELAY=0
MIMALLOC_PURGE_DECOMMITS=1
LLVM_SYS_231_PREFIX=
PATH=/usr/bin:/bin
RUST_LOG=
LIBRARY_PATH=
SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=
SIMPLE_BOOTSTRAP=1
SIMPLE_ABI_POLICY=
SIMPLE_PLUGIN_MANIFEST_POLICY=
SIMPLE_KERNEL_K1_POLICY=
SIMPLE_COVERAGE_CUTOVER_STATE=
SIMPLE_K1_COMPOSITION_SHA256_BEFORE=
SIMPLE_NO_DEPRECATED_WARNINGS=1
SIMPLE_NATIVE_BUILD_RUST=1
SIMPLE_NO_STUB_FALLBACK=1
SIMPLE_BUILD_PROGRESS_EVENTS=
SIMPLE_FRONTEND_CACHE=1
SIMPLE_FRONTEND_CACHE_DIR=/frontend
SIMPLE_HIR_CACHE=1
SIMPLE_HIR_CACHE_DIR=/hir
SIMPLE_PHASE2_COMPATIBILITY_MANIFEST_WRITE=
SIMPLE_PHASE3_COMPATIBILITY_CACHE_ROOT=
SIMPLE_BINARY=/bin/sh""".splitlines()]
LEGACY_ARGV = [item.encode() for item in (
    "native-build", "--target", "aarch64-unknown-linux-gnu",
    "--backend", "cranelift", "--runtime-bundle", "core-c-bootstrap",
    "--source", "", "--source", "src/compiler", "--source", "src/app",
    "--source", "src/lib", "--entry-closure", "--threads", "1",
    "--cache-dir", "", "--low-memory", "--mode", "dynload",
    "--entry", "src/app/cli/bootstrap_main.spl", "--runtime-path", "", "-o", "",
)]
LEGACY_IDENTITY = digest(LEGACY_ENV + LEGACY_ARGV).encode()
resume_start = RESUME.index("stage2_args=$(bootstrap_stage3_args_sha256")
resume_hash = RESUME[resume_start:RESUME.index("bootstrap_stage3_verify_sanity_evidence_receipt", resume_start)]
route_start = COMMAND.index("        /bin/sh -c '\n            if [ \"${SIMPLE_BOOTSTRAP_SESSION_ID+x}")
hermetic_route = COMMAND[route_start:COMMAND.index("\n    ) >", route_start)]
replay_start = REPLAY.index("stage2_recorded_diagnostics=")
replay_policy = REPLAY[replay_start:REPLAY.index("\nexpected_env_names=", replay_start)]

with tempfile.TemporaryDirectory(prefix="stage2-diagnostic-contract-") as directory:
    tmp = Path(directory)
    capture = tmp / "vector"
    transcript = tmp / "transcript"
    snapshot = tmp / "memory.events"
    names = set(re.findall(r"\$\{([A-Za-z_][A-Za-z_0-9]*)", control + runner))
    values = {name: "" for name in names if name not in DIAGNOSTICS}
    values.update(PLATFORM="aarch64-unknown-linux-gnu", stage_build_path="/usr/bin:/bin",
                  NATIVE_LOW_MEMORY="1", stage2_refusal_log=str(tmp / "refusal"), jobs="1",
                  backend="cranelift", bootstrap_mode="dynload", stage2_seed_absolute="/bin/sh")
    # Remove empty optional exports: absence has distinct semantics.
    values.pop("SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB", None)
    boundary = f"""
absolute_path() {{ printf '%s\\n' "$1"; }}
bootstrap_stage3_run_transcribed() {{ printf '%s\\0' "$@" > {shlex.quote(str(capture))}; }}
"""

    def vector(diagnostics, *, mutate="", overrides=None):
        selected = dict(values)
        selected.update(diagnostics)
        selected.update(overrides or {})
        result = shell(setup(selected) + boundary + control + runner + "\n" + mutate +
                       '\nbootstrap_run_stage2_native || exit $?\nprintf "%s\\n" "$stage2_build_args_sha256"\n')
        if result.returncode:
            return result, None, None, None
        vec = capture.read_bytes().split(b"\0")[:-1][6:]
        split = vec.index(b"--")
        env, argv = vec[:split], vec[split + 2:]
        assert result.stdout.decode().strip() == digest(env + argv), "hash/execution vector mismatch"
        return result, env, argv, result.stdout.strip()

    cases = ({}, {DIAGNOSTICS[2]: "1"},
             {DIAGNOSTICS[0]: str(snapshot), DIAGNOSTICS[1]: "run-1"},
             {DIAGNOSTICS[0]: str(snapshot), DIAGNOSTICS[1]: "run-1", DIAGNOSTICS[2]: "1"},
             {DIAGNOSTICS[0]: str(tmp / "other.events"), DIAGNOSTICS[1]: "run-1"},
             {DIAGNOSTICS[0]: str(snapshot), DIAGNOSTICS[1]: "run-2"})
    hashes = []
    for diagnostics in cases:
        result, env, argv, identity = vector(diagnostics)
        assert result.returncode == 0, result.stderr.decode()
        hashes.append(identity)
        if not diagnostics:
            assert env == LEGACY_ENV, "legacy environment bytes/order changed"
            assert argv == LEGACY_ARGV, "legacy argument bytes/order changed"
            assert identity == LEGACY_IDENTITY, "legacy identity changed"
        # The existing canonical shell route is executed literally, including
        # its env -i and explicit-assignment export loop. No compiler is run.
        probe = 'printf "%s\\n" "${SIMPLE_MEM_SNAPSHOT_FILE-absent}" "${SIMPLE_EVIDENCE_RUN_ID-absent}" "${SIMPLE_M4_WORK_RECEIPT-absent}" "${UNLISTED_DIAGNOSTIC-absent}"'
        host = setup(dict(bootstrap_stage3_run_home=str(tmp), bootstrap_stage3_run_tmpdir=str(tmp),
                          bootstrap_stage3_run_path="/usr/bin:/bin", UNLISTED_DIAGNOSTIC="must-not-leak"))
        transported = shell(host + "export UNLISTED_DIAGNOSTIC\nset -- " + quoted(env + [b"--", b"/bin/sh", b"-c", probe.encode()]) + "\n" + hermetic_route)
        assert transported.returncode == 0, transported.stderr.decode()
        assert transported.stdout.decode().splitlines() == [diagnostics.get(k, "absent") for k in DIAGNOSTICS] + ["absent"]
        # Use the real transcript writer, then reconstruct the production
        # Stage3 reader's exact args hash even after evidence exists on disk.
        write = shell("bootstrap_stage3_write_command_transcript " + quoted([str(transcript), str(tmp), str(tmp), str(tmp), "/usr/bin:/bin", *env, b"--", b"/bin/sh", *argv]))
        assert write.returncode == 0, write.stderr.decode()
        if DIAGNOSTICS[0] in diagnostics:
            Path(diagnostics[DIAGNOSTICS[0]]).write_text("completed evidence\n")
        recorded = f"stage2_transcript={shlex.quote(str(transcript))}\n"
        recorded += 'stage2_env_value() { bootstrap_stage3_transcript_explicit_env_value "$stage2_transcript" "$1"; }\n'
        recorded += 'stage2_recorded_diagnostics=$(bootstrap_stage3_stage2_transcript_diagnostics "$stage2_transcript") || exit 1\n'
        recorded += setup(dict(bootstrap_stage2_hir_env="1", stage2_hir_cache="1", stage2_hir_cache_dir="/hir", stage2_progress=""))
        recovered = shell(setup(values) + recorded + "set -- " + quoted(argv) + "\n" + resume_hash + '\nprintf "%s\\n" "$stage2_args"')
        assert recovered.returncode == 0, recovered.stderr.decode()
        assert recovered.stdout.strip() == identity, "admission reconstruction changed identity"
        replay = shell(f"transcript={shlex.quote(str(transcript))}\nresume_fail() {{ exit 9; }}\n" + replay_policy)
        assert (replay.returncode == 0) == (DIAGNOSTICS[0] not in diagnostics), "snapshot replay must fail closed"
        if DIAGNOSTICS[0] in diagnostics:
            Path(diagnostics[DIAGNOSTICS[0]]).unlink()  # temporary test evidence only
    assert len(set(hashes)) == len(hashes), "diagnostic identity failed to bind a value"

    pair = {DIAGNOSTICS[0]: str(snapshot), DIAGNOSTICS[1]: "run-1"}
    invalid = [{k: ""} for k in DIAGNOSTICS]
    invalid += [{DIAGNOSTICS[2]: x} for x in ("0", "yes", "1 1")]
    invalid += [{DIAGNOSTICS[0]: str(snapshot)}, {DIAGNOSTICS[1]: "run-1"}]
    invalid += [{**pair, DIAGNOSTICS[1]: x} for x in ("x y", "x\ny", "x=1", "x/1", "x" * 128)]
    invalid += [{**pair, DIAGNOSTICS[0]: x} for x in ("relative", "/", str(tmp / ".." / "x"), str(tmp / "x y"), str(tmp / "*.events"))]
    for diagnostics in invalid:
        assert vector(diagnostics)[0].returncode != 0, f"invalid request accepted: {diagnostics}"
    assert vector({**pair, DIAGNOSTICS[1]: "x" * 127})[0].returncode == 0
    assert vector(pair, overrides={"NATIVE_LOW_MEMORY": "0"})[0].returncode != 0
    snapshot.write_text("preserve")
    assert vector(pair)[0].returncode != 0
    snapshot.unlink()
    alias = tmp / "alias"
    alias.symlink_to(tmp, target_is_directory=True)
    assert vector({**pair, DIAGNOSTICS[0]: str(alias / "snapshot")})[0].returncode != 0
    snapshot.symlink_to(tmp / "missing")
    assert vector(pair)[0].returncode != 0
    snapshot.unlink()
    tmp.chmod(0o755)
    assert vector(pair)[0].returncode != 0
    tmp.chmod(0o700)
    assert vector(pair, mutate=f"printf occupied > {shlex.quote(str(snapshot))}")[0].returncode != 0
    snapshot.unlink()
    for addition in ("SIMPLE_M4_WORK_RECEIPT=1", "EXTRA_DIAGNOSTIC=1"):
        assert vector({DIAGNOSTICS[2]: "1"}, mutate=f'stage2_diagnostic_env="$stage2_diagnostic_env {addition}"')[0].returncode != 0

    def record(name, value):
        payload = name + "=" + value
        return f"explicit-env:{len(payload)}:{payload}\n"

    good = record(DIAGNOSTICS[0], str(snapshot)) + record(DIAGNOSTICS[1], "run-1") + "argv:12:--low-memory\n"
    for malformed in (good + record(DIAGNOSTICS[0], str(snapshot)),
                      good + record(DIAGNOSTICS[0].lower(), str(snapshot)),
                      good.replace("explicit-env:", "explicit-env:invalid:", 1),
                      good.replace("run-1", "run-2-long"),
                      good.replace("argv:12:--low-memory\n", ""),
                      record(DIAGNOSTICS[1], "run-1") + record(DIAGNOSTICS[0], str(snapshot)) + "argv:12:--low-memory\n",
                      record(DIAGNOSTICS[2], "0"), record(DIAGNOSTICS[2], "")):
        transcript.write_text(malformed)
        assert shell("bootstrap_stage3_stage2_transcript_diagnostics " + shlex.quote(str(transcript))).returncode != 0, malformed
    for descriptor in ("EXTRA_DIAGNOSTIC", "SIMPLE_M4_WORK_RECEIPT SIMPLE_M4_WORK_RECEIPT", "SIMPLE_EVIDENCE_RUN_ID"):
        assert shell("bootstrap_stage3_stage2_canonical_env_names linux '' '' " + shlex.quote(descriptor)).returncode != 0

print("PASS: Stage2 diagnostic env-i transport, exact hash/transcript/resume identity, legacy compatibility, exclusive ownership, malformed/duplicate/extra controls")

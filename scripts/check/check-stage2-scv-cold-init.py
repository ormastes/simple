#!/usr/bin/env python3
"""Exercise actual Stage 2 shell vectors and fail-closed cold-init readers."""
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
control = SOURCE[SOURCE.index("  stage2_cold_init_env=\n"):
                 SOURCE.index("  stage3_evidence_run_id=", SOURCE.index("  stage2_cold_init_env=\n"))]
start = SOURCE.index("  bootstrap_run_stage2_native() {")
runner = SOURCE[start:SOURCE.index("\n  set +e", start)]
resume_source = (ROOT / "scripts/bootstrap/resume-stage3-from-admitted.sh").read_text()
resume_hash = resume_source[resume_source.index("stage2_args=$(bootstrap_stage3_args_sha256"):
                            resume_source.index("bootstrap_stage3_verify_sanity_evidence_receipt", resume_source.index("stage2_args=$(bootstrap_stage3_args_sha256"))]
replay_source = (ROOT / "scripts/bootstrap/resume-stage2-from-cache.sh").read_text()
replay_policy = replay_source[replay_source.index('if [ "$stage2_recorded_cold_init" = 1 ]; then'):
                              replay_source.index('\nSIMPLE_ABI_POLICY=', replay_source.index('if [ "$stage2_recorded_cold_init" = 1 ]; then'))]
prefix = f". {shlex.quote(str(LIB / 'authority.shs'))}\n. {shlex.quote(str(LIB / 'command-snapshot.shs'))}\n"


def shell(code, *, env=None):
    return subprocess.run(["sh", "-c", prefix + code], env=env,
                          capture_output=True, check=False)


def assignment_record(value):
    payload = "SIMPLE_SCV_INVENTORY_COLD_INIT=" + value
    return f"explicit-env:{len(payload)}:{payload}\n"


with tempfile.TemporaryDirectory(prefix="stage2-scv-contract-") as directory:
    tmp = Path(directory)
    for platform in ("aarch64-unknown-linux-gnu", "aarch64-unknown-freebsd"):
        hashes = []
        for value in ("", "1"):
            names = set(re.findall(r"\$\{([A-Za-z_][A-Za-z_0-9]*)", control + runner))
            values = {name: "" for name in names}
            values.update(PLATFORM=platform, SIMPLE_SCV_INVENTORY_COLD_INIT=value,
                          stage_build_path="/usr/bin:/bin", NATIVE_LOW_MEMORY="0",
                          stage2_refusal_log=str(tmp / "refusal"), jobs="10",
                          backend="llvm", bootstrap_mode="dynload")
            initial = "\n".join(f"{key}={shlex.quote(val)}" for key, val in values.items())
            capture = tmp / "vector"
            # Stub only the execution boundary: evaluate the real launcher,
            # its name guard, and its independently constructed args hash.
            boundary = f"""
absolute_path() {{ printf '%s\\n' "$1"; }}
bootstrap_stage3_run_transcribed() {{ printf '%s\\0' "$@" > {shlex.quote(str(capture))}; }}
"""
            result = shell(initial + "\n" + boundary + control + runner +
                           '\nbootstrap_run_stage2_native || exit $?\nprintf "%s\\n" "$stage2_build_args_sha256"\n')
            assert result.returncode == 0, result.stderr.decode()
            vector = capture.read_bytes().split(b"\0")[:-1][6:]
            split = vector.index(b"--")
            environment = vector[:split]
            argv = vector[split + 2:]  # omit executable, just like args hash
            digest = hashlib.sha256(b"".join(str(len(x)).encode() + b":" + x + b"\n"
                                             for x in environment + argv)).hexdigest()
            assert result.stdout.decode().strip() == digest, "hash/execution vector mismatch"
            hashes.append(digest)
            child = subprocess.run(["env", "-i", *[x.decode() for x in environment],
                                    "/bin/sh", "-c", 'printf "%s" "${SIMPLE_SCV_INVENTORY_COLD_INIT:-absent}"'],
                                   capture_output=True, check=True)
            assert child.stdout.decode() == (value or "absent")
            recorded = tmp / "recorded"
            recorded.write_text("".join(f"explicit-env:{len(x)}:{x.decode()}\n" for x in environment))
            setup = f"""
stage2_transcript={shlex.quote(str(recorded))}
stage2_env_value() {{ bootstrap_stage3_transcript_explicit_env_value "$stage2_transcript" "$1"; }}
stage2_recorded_cold_init=$(bootstrap_stage3_stage2_transcript_cold_init "$stage2_transcript") || exit 1
bootstrap_stage2_hir_env=1
stage2_hir_cache=1
stage2_hir_cache_dir=/hir
stage2_progress=
set -- {' '.join(shlex.quote(x.decode()) for x in argv)}
"""
            recovered = shell(initial + "\n" + setup + resume_hash + '\nprintf "%s\\n" "$stage2_args"')
            assert recovered.returncode == 0, recovered.stderr.decode()
            assert recovered.stdout.decode().strip() == digest, "Stage 3 receipt reconstruction mismatch"
            replay = shell(f"stage2_recorded_cold_init={shlex.quote(value)}\n"
                           "SIMPLE_SCV_INVENTORY_COLD_INIT=yes\n" + replay_policy +
                           '\nprintf "%s" "${SIMPLE_SCV_INVENTORY_COLD_INIT:-absent}"')
            assert replay.returncode == 0 and replay.stdout.decode() == (value or "absent")
        assert hashes[0] != hashes[1], "opt-in must change admitted args hash"
    for bad in ("0", "yes", "true", "1 1"):
        result = shell(f"SIMPLE_SCV_INVENTORY_COLD_INIT={shlex.quote(bad)}\n" + control)
        assert result.returncode != 0, f"invalid caller value accepted: {bad}"

    transcript = tmp / "transcript"
    read = f"bootstrap_stage3_stage2_transcript_cold_init {shlex.quote(str(transcript))}"
    for record, expected in (("", ""), (assignment_record("1"), "1")):
        transcript.write_text(record)
        result = shell(read, env={**os.environ, "SIMPLE_SCV_INVENTORY_COLD_INIT": "yes"})
        assert result.returncode == 0 and result.stdout.decode().strip() == expected
    for record in (assignment_record("0"), assignment_record(""), assignment_record("yes"),
                   assignment_record("1") * 2, "explicit-env:1:SIMPLE_SCV_INVENTORY_COLD_INIT=1\n",
                   assignment_record("1") + "explicit-env:invalid:SIMPLE_SCV_INVENTORY_COLD_INIT=1\n",
                   "explicit-env:invalid:SIMPLE_SCV_INVENTORY_COLD_INIT=1\n"):
        transcript.write_text(record)
        assert shell(read).returncode != 0, f"invalid recorded opt-in accepted: {record!r}"
    for platform in ("aarch64-unknown-linux-gnu", "aarch64-unknown-freebsd",
                     "aarch64-apple-darwin", "x86_64-pc-windows-msvc", "x86_64-pc-windows-gnu"):
        legacy = shell(f"bootstrap_stage3_stage2_canonical_env_names {platform}").stdout.decode().strip()
        opted = shell(f"bootstrap_stage3_stage2_canonical_env_names {platform} 1").stdout.decode().strip()
        assert opted == legacy + " SIMPLE_SCV_INVENTORY_COLD_INIT"
        assert shell(f"bootstrap_stage3_stage2_canonical_env_names {platform} yes").returncode != 0

print("PASS: Stage 2 SCV cold-init execution/hash binding, legacy compatibility, and invalid/duplicate rejection")

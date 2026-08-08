# Bootstrap seed fingerprint per-file process storm

Status: fixed by `/root/stage4_log_triage` on 2026-08-03.

The x86 Stage 4 bootstrap spent 181 seconds in the pre-build `fingerprint`
phase and exited before creating its main build log. The authority inventory
contained 43,191 files: 40,740 tracked vendored inputs and 2,451 other files
under `src/compiler_rust`.

`bootstrap_stage3_seed_inputs_fingerprint` correctly includes every vendored
byte, but its loop calls `bootstrap_stage3_hash_file` once per path. On hosts
with `sha256sum`, every file therefore launches both `sha256sum` and `awk`, or
roughly 86,000 processes for this checkout.

The fix must preserve the complete, deterministic `hash path` authority and
content-change sensitivity. It may batch tools that accept multiple paths,
while retaining the existing one-file fallback for host hash tools that cannot
emit a portable multi-file record.

The focused regression passes 320 paths through no more than four hash-tool
invocations, repeats byte-identically, changes one record when one input
changes, and preserves an adjacent path containing spaces and metacharacters.
A bounded real-inventory run emitted all 43,191 records in 2.70 seconds with
3,840 KiB maximum RSS, versus the observed 181-second pre-fix fingerprint
phase.

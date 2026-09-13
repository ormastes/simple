# Windows Cargo MSVC output paths and descendant wait

**Status:** OPEN (unverified 2026-09-12)

The Phase 1 Rust seed build exited 101 while building `libmimalloc-sys`.
MSVC emitted C1083 with an empty compiler-generated-file name and `Invalid
argument`. Its native `/Fo` output path was 260 characters long (266 in cc-rs
debug output, which escapes the backslashes).

A tiny isolated C fixture reproduced the cause: a 119-character output path
compiled successfully and a 272-character output path failed with the same
C1083. Repeating with valid native `TEMP` and `TMP` directories preserved both
outcomes. Missing `TMP` was not the cause.

Windows bootstrap now selects `repo/build/c/<full input fingerprint>` for
Cargo outputs. HOME, configuration, logs and authority receipts retain their
existing locations. On Windows, the shared Rust authority lock is acquired before workspace
preparation and the first Cargo operation, and held across all Cargo calls,
fingerprint checks, immutable snapshot/publication and runtime normalization.
Identical inputs reuse the same target even when the log output root
changes; different fingerprints remain isolated. Existing caches are neither
moved nor removed. The first build using the new location may rebuild files;
subsequent retries reuse it.

Lock order is bootstrap output ownership, then Rust authority ownership. Early
transaction recovery releases authority ownership before the build; later
publication/normalization acquisitions revalidate the same handle. There is no
second target lock or reverse-order wait. Different Rust fingerprints in one
Windows checkout intentionally serialize; independent checkouts have separate
caches and locks. Unix keeps its private per-output Cargo caches and acquires
the authority lock only at the existing publication/normalization boundary.
Normal success/failure releases owned locks through the existing
cleanup. A signal retains ownership until the entire recorded process group is
dead, preventing surviving writers from racing recovery. Locks have no lease
expiry or heartbeat: stale recovery uses PID/start identity and process-group
liveness, so a long Cargo build cannot lose ownership merely with elapsed time.

The native target prefix must fit in 120 bytes, reserving another 120 bytes for
Cargo/cc-rs output nesting under a conservative 240-byte budget. Longer checkout
roots fail before Cargo launch with an actionable diagnostic. This reservation
covers the observed libmimalloc-sys path; it is not a claim that arbitrary future
crate-generated filenames can never exceed the Windows path limit.

The delayed process receipt had a separate explanation. A read-only handle
snapshot of the same tiny fixture showed a terminated root process, output-pipe
EOF, and one active job member: `vctip.exe`, the MSVC telemetry descendant.
The original supervisor naturally published its complete native exit-101
receipt approximately 15 minutes after the last Cargo output. Job containment
and telemetry settings are unchanged. This descendant can still delay receipt
publication; job-wide waiting is required by the existing collector contract.

Local diagnostic evidence from the combined integration checkout:
`build/native_probe/cl-receipt-6db2f72847be4b1a90d168d6f4c13813/`, including
`handle-observation.json`, four compiler logs and a timeout receipt proving the
25-second probe reaped its remaining descendant. No full bootstrap was used
for this regression.

Focused validation: `bootstrap_windows_cargo_path_budget_test.shs` and
`bootstrap_rust_authority_incremental_cache_contract_test.shs` passed. The
combined-checkout target prefix is 119 bytes and its realistic object path is
221 bytes (239 with the full reserved suffix). In the fix checkout, native
MSVC compiled at the configured 211-character object path with exit 0 and
produced a 794-byte x64 COFF object. Its 10-second bounded diagnostic terminated
the remaining telemetry descendant and retained native exit 0 in
`build/native_probe/configured-cargo-cl/command.env`.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.

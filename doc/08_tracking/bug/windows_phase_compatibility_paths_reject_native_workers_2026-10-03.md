# Windows frozen frontend entries rejected before parsing

Status: fix under native verification; no runtime or release admission.

On Windows, the LLVM Stage2 candidate `452b8a2d511228114ad7019b74bdba19f33191be7a16872da226a7ad0b39dbc3`
built from source `3fa01c989b2573de9e19287aed30f2e7a4da6b0d` linked 1,158 modules successfully.
Its corrected self-hosted Hello profile inherited a physically verified immutable
SCV snapshot, used two frontend shards and 40 backend jobs, and failed before
parsing with `frozen cold entry rejected: unsupported-host`. Four independent
full-CLI, test-runner, MCP and LSP/MCP builds reproduced source-loading failure.
No Hello run or dependent Phase3 build passed.

The driver reads frozen frontend entries through
`phase_compatibility_existing_artifact_io_v1`. Its directory and manifest
admission owners unconditionally rejected hosts whose separator was not `/`.
This rejected legitimate Windows paths independently of the earlier memory
failure and SCV refresh-lock contention, which remain preserved evidence.

The repair admits ordinary drive-absolute Windows paths after separator-only
normalization. Canonical spelling, root containment, regular no-follow leaves,
occupied destinations and bounded reads remain required. Every directory
ancestor must be a real directory without a reparse point: Windows `_fullpath`
alone is lexical and cannot provide the POSIX `realpath` protection. UNC/device
names, streams, reserved device components, empty/dot components and trailing
dot/space aliases remain rejected. POSIX admission retains its existing rules.

Windows Stage2's narrow runtime archive lacked the already-defined
`rt_dir_is_real_no_follow` ABI. The existing secure-staging provider supplies
that function on Windows, using its bounded UTF-8/extended-path conversion and
directory/non-reparse attribute checks. Linux retains its existing provider.

The first focused native probe compiled two modules successfully but failed its
Windows-host prerequisite: `runtime_native.c` returned `/` unconditionally from
`rt_path_separator`, even on Windows. This small core-C closure compiles the C
runtime from source; it did not consume the supplied diagnostic Rust runtime
archive. The C provider now selects `\\` on Windows and `/` elsewhere. Both
runtime routes therefore describe the same host, and their evidence is kept
distinct. The first run is a failure, not a skipped or successful Windows test.

The focused smoke checks actual filesystem objects, a real directory junction,
reads, positive admissions and alias/containment rejections. Its harness must
fail if the junction fixture cannot be created. Bootstrap-produced focused
evidence does not substitute for the full compatibility specifications,
compiler/library checks, core/MCP smoke, Stage2 admission or release verification.

Focused cycle2 passed21 actual Windows oracles, zero failures and raw status0.
It reused one cached module and compiled one, with zero compile failures; build
RSS peaked at1,186,276KiB and execution at14,352KiB against the5,859,375KiB cap.
The native executable SHA-256 is
`ffa87ff4e10390e8d2c84f5a43594c3185c5e630dd13a69e22dfaa0ec0d591a8`.
No passing criterion is rerun without a changed input. The generated result's
inherited runtime-authority description is corrected in the separate
`runtime-route-correction.json`; the original receipt remains preserved.

Evidence roots: `build/native_probe/llvm-repaired3fa-inherited-scv-hello40-attempt1`,
`build/native_probe/llvm-repaired3fa-inherited-core40-attempt1`, and the distinct
`build/native_probe/windows-phase-path-io-proof1` and `windows-phase-path-io-proof2`
under the preserved Windows
phase2 worktree. The focused runtime replacement is diagnostic-only and records
the original archive, replaced member, source and output hashes without copying
an authority stamp from the original archive.

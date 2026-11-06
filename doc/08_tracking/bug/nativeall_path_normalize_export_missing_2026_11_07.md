# Nativeall path normalize export missing

Status: **fix implemented; verification pending (P1/open)**. Canonical root claim remains fixing under `01a1afac/nativeall-path-normalize`; this isolated row does not close it.

The retained Windows nativeall link reports unresolved `rt_path_normalize`. Existing C runtime_core_io_exports.c provides lexical normalization, while the Rust owning runtime lacked that export. Base: `bfcab1cde567ad9efa4ced3bb2c67299587dde14`.

The new Rust RuntimeValue export copies a registered RuntimeString into a bounded stack buffer under the registry guard, releases the guard before allocating, checks the full pre-NUL length is below 4096 and validates UTF-8, then reproduces the C lexical algorithm. It preserves ASCII drive handling, both separators, rooted parent components, body_start/pop behavior, trailing separators and empty-input dot behavior. Invalid/wrong-kind values return an empty managed string. It performs no filesystem resolution and leaves other path APIs unchanged.

Reviewed production Git blob: `33f916a64e5d97d071792ff9bef42ece24b81e99`; six-test blob: `beb68f6824e23bf8041222d670da13f15f9775ff`. Both remained identical after materialization and NTFS compression. Only the owned ordinary private cache was compressed; manifest contents were verified before/after, without hardlinks or shared writes.

## Verification

Changing/verify budget: **2/6 attempts**, no automatic third retry.

Attempt 1: guarded Cargo exited 101 before tests because sparse local workspace dependencies were missing (`libmimalloc-sys`; independent manifest review also found `inkwell`). Restored only those two tracked base dependencies; nested manifest paths existed. No source repair or broad vendor copy.

Attempt 2: exact filter `value::sffi::file_io::path::path_normalize_tests::`, `--test-threads=1`, offline locked default cpu-simd bootstrap-profile Windows gnullvm runtime tests. **6 passed, 0 failed, 1414 filtered**; compile 2m11s. Named cases cover exact lexical behavior, full-length/NUL ordering, byte boundaries, invalid/wrong-kind values, malformed UTF-8 after NUL, and owned snapshot surviving input release.

Frozen Windows Job guard SHA256 `3c72d99ecbbaf704749261e23ebc4865fbf8f4b4f6252614fab0ce003c442293`; child exit 0, resource_error none, 8GiB memory / 2 CPUs / 1200s / 32MiB log / 3GiB target / 2GiB reserve unchanged. Peak committed 1276121088, RSS 1174376448, target 279781376 bytes. Log SHA256 `753880725c5548beeda1b177f619ce69a0445e7b5de33d89390d4021ff157121`.

Host-local immutable attempt evidence: `C:/dev/simple/.git/worktrees/nativeall-path-normalize-d88f/evidence/runtime-owner-attempt{1,2}.{log,receipt.env,command.json}`; input repair and compression records are in the same evidence directory.

Nativeall link, P2 native behavior, pure-Simple self-hosted regression, SSpec and core/MCP checks: **UNRUN**. Runtime-owner Cargo evidence is not compiler/native acceptance. Source-only unsafe inventory FAIL is reused only with 44954 owned SPL + two audit-script input equality; it excludes this Rust boundary and is not qualification. No audit rerun or baseline increase.

Provider input/output/cache-read/cache-create tokens=unavailable; comparable cohort average=unavailable; ratio=unavailable. Draft only; not ready/merged/resolved.

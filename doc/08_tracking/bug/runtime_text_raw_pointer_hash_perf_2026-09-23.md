# Raw-pointer text blocks linear-time runtime hash qualification

Status: OPEN; blocks merge/admission of hash draft PR #1412.

`runtime_text_hash_v1` currently indexes `value.byte_at(index)`. Length-bearing
text uses O(1) byte reads, but the legacy raw-pointer branches of C
`src/runtime/runtime_native.c:rt_string_byte_at` and pure-Simple
`src/runtime/simple_core/core_string.spl:rt_string_byte_at` scan for NUL per
read, yielding O(n²) work. NUL-containing text requires a length-bearing value.

Do not replace this loop with `.bytes()` blindly: the C and pure-Simple
`rt_string_bytes` implementations return an empty array for unrecognized raw
text. Pure-Simple concat and slice also reject that representation. Such a
substitution would change hash results rather than safely optimize them.

## Focused fail-closed probe

`test/fixtures/compiler/runtime_text_hash_raw_perf.spl` obtains a borrowed
pointer through the existing `rt_string_data` ABI, retaining its owning text,
then checks byte length before timing equal hashes at 16/32/64 KiB. This is a
test-only machine-word ABI declaration, not a production foreign hash fallback.

With admitted Stage2 `70748fd0` SHA256
`7f6283bc9a2b7e9d7ef7078b5c3bc7fbba49a54d3d6b61f83bb3cd0540a55821`, source
main `806f57ffbd88` plus hash fix `fc4c0f26a6f`, Cranelift compilation/link
passes (2 modules, 72 KB, 3.77 s, 139378688-byte compiler RSS). Execution fails
closed before timing: `raw-text-abi-length-mismatch`, exit 1, RSS 8683520 bytes.
No raw-pointer throughput number or performance parity claim is valid yet.
Receipts remain in `build/evidence/runtime-text-hash-v1/raw-*.log`.

The admitted binary's `--help` exposes only `compile` and `native-build`, not
`run`/`optimize`. The optimizer app and general SPipe runner are therefore
TEST_BLOCKED under this tool's admission; no seed fallback was attempted.

## Required repair and admission

Establish a portable one-time text-data/length conversion with a safe lifetime,
or a one-pass byte materialization supporting both representations. A bounded
allocation is acceptable if measured and documented; new per-byte NUL scans,
runtime-specific casts, and a C hash replacement are not acceptable fixes.
First qualify the borrowed raw-text ABI/length probe, then run the same hash
vectors and scaling fixture before/after. Require exact UTF-8/NUL behavior,
linear scaling, bounded RSS, an admitted optimizer run, and Astra review before
removing the draft blocker. Current-main/full-CLI admission remains separate.

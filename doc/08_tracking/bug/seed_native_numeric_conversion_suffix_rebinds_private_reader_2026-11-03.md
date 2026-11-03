# Seed native numeric conversion suffix rebinds a private reader

- Priority: P0 (ARM64 Linux bootstrap admission blocker)
- Status: fixing; no post-fix native pass claimed
- Owner: `src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`; suffix lookup in adjacent `imports.rs`
- Observed: 2026-11-03, ARM64 Linux attempt 8 Phase 2 sanity `p2_add` native build
- Repair owner: bootstrap_arm64_lead; database owner: bug_db_lead

## Failure and evidence

Phase 2 linked, but its sanity compiler segfaulted while encoding the frontend SPAB cache through XXH3. Disassembly at `0x1379870` moves array length into `x0`; `0x1379880` calls `compiler__backend__introspection__elf_artifact_gate___u64` instead of performing the numeric conversion in `src/lib/common/crypto/xxh3.spl`, `_len129to240_64`. The ELF reader expects an array plus an offset; the failure presents integer 176 as its array pointer. This is wrong call-target resolution, not a demonstrated XXH3 algorithm defect.

`native_project/imports.rs` suffix extraction indexes a mangled private `___u64` as `u64`; underscore splitting of `to_u64` can select it. `resolve_call_target` has no numeric-conversion guard, and primitive-qualified static method calls bypass the existing unqualified guard. Both routes require protection while retaining legitimate custom-owner conversions and authored exact imports. The emitted callee is proven; the original failing MIR variant has not been identified.

Evidence retained at `/tmp/aspect-fix-rr-attempt8-core-20261103/backtrace.txt` and `xxh3-disassembly.txt`; independent analysis: `/tmp/parallel-three-tracks-20261103/bootstrap/crash-evidence.md`. These are session-local artifacts, not portable CI admission. GDB warns the core may not match the specified executable because its original mapped pathname is unavailable; artifact identity must be verified before formal core admission. The incorrect direct-call disassembly is independent evidence.

## Acceptance

1. Resolver regressions cover bare and primitive-qualified numeric conversions for CallTarget and MethodCallStatic with a conflicting real private byte reader.
2. Negative controls retain custom-owner conversion and exact authored import resolution.
3. Native compiler fixture executes typed, inferred, chained and signed-roundtrip conversions plus the private reader's own correctness checks.
4. The repaired producer rebuilds Phase 2 and passes real compiled Hello/sanity execution before dependent phases. Record exact source, producer, runtime, target and cache lineage.

Repair and acceptance are in progress. A source patch, passing resolver unit test, or linked Phase 2 alone does not close this record. macOS is not asserted reproduced; the resolver is shared.

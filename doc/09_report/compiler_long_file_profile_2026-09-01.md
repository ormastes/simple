# Compiler long-file profile — 2026-09-01

## Result

This is **provisional diagnostic evidence**, not an admitted performance result.
No admitted Phase-2 runtime was available.  The measured R11 candidate is marked
`simple.rejected` and fails correctness on this workload.

The selected owned source was
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, the largest file under
`src/compiler` at this revision: 307,824 bytes and 5,150 lines.

| Attempt | Wall | User | System | Max RSS | Cache | Result |
|---|---:|---:|---:|---:|---|---|
| cold | 128.27 s | 123.10 s | 3.96 s | 4,316,408 KiB | miss; no artifact written | FAIL: SIGSEGV in HIR after unresolved types |
| warm attempt | at least 63.83 s | unavailable | unavailable | unavailable | no reusable artifact existed | terminated externally during parse; no timing trailer or output |

There is therefore no valid warm-hit number and no defensible before/after
speedup claim.  The cold failure did not publish an SMF or cache entry.  A
second, non-identical output attempt reused the same cache scope, but performed
closure discovery and parsing again.  It reached only the third parsed module
at 63.825 s.  Repeating it would violate the bounded profiling rule without
providing a warm-cache measurement.

## Identity and commands

- Source revision: `b7839b1f042638bb060e62a0099004c30c680ee9`
- Rejected R11 SHA-256:
  `e57c9b15997dfeed31cc9e3e805d8bea0ef0bd030efd63039eca6ece3d519401`
- Runtime:
  `/mnt/fast/bootstrap-stage2-integrated-migration-20260901-r11/stage2/x86_64-unknown-linux-gnu/simple.rejected`
- Both attempts used `SIMPLE_LIB=src`, cache scope
  `long-file-profile-r11`, and
  `SIMPLE_NATIVE_BUILD_CACHE_DIR=build/profile-long-file/cache`.
- Cold command shape:
  `/usr/bin/time -v timeout 240s env ... simple.rejected compile <file> --format=smf --output=<cold-output>`
- Warm-attempt command shape used a distinct output and a 180-second bound while
  preserving the exact cache scope.

Raw evidence is intentionally kept under ignored
`build/profile-long-file/{cold,warm}` in this worktree.

## Phase profile

Cold cumulative milestones:

| Phase | Cumulative time | Increment/evidence |
|---|---:|---:|
| initial closure start | 7.791 s | startup before closure traversal |
| source closure complete (150 modules) | 49.291 s | one closure interval consumed 35.707 s |
| load sources complete (193 inputs) | 52.532 s | 3.241 s |
| parse complete | 121.569 s | about 68.987 s including surface work |
| HIR failure/crash | 128.27 s | about 6.7 s after parse completion |

The largest recorded interval was source-closure discovery around
`src/lib/nogc_async_mut/array.spl`: **35.707 s**.  `surface_freeze` was the next
large aggregate interval at **10.169 s**.  Parsing the three largest MIR files
took 2.613 s, 2.935 s, and 3.013 s respectively.

## Correctness and optimization conclusion

The candidate emitted unresolved-type HIR diagnostics including
`DriverManifestAttr`, `VhdlHardwareMetadata`, `ExportAttr`, and `FunctionAttr`,
then crashed with signal 11.  The result is not correct and cannot qualify as a
performance pass.

The immediate bottleneck is repeated whole-closure discovery/parsing rather
than the selected file alone: one-file compilation expands to 150 compiler
modules and 193 loaded inputs.  Cache publication is all-or-nothing, so a late
HIR failure leaves the following attempt cold.  Before optimizing individual
MIR routines, the compiler needs:

1. fail-closed HIR diagnostics without a segmentation fault;
2. an admitted Phase-2 runtime;
3. reusable, revision-bound frontend closure/parse cache entries, including
   safe negative/incomplete-entry rejection; and
4. a rerun of this exact workload once cold and once warm, with successful SMF
   checksum equality.

For context only, the broader cached bootstrap was **103.2 s** in R10 (3
compiled, 819 cached) and **115.8 s** in R11 (4 compiled, 818 cached).  Those are
different build revisions/work sets and are not a valid file-level regression
comparison.

## Follow-up optimization

The closure profile led to a pure-Simple cache-access fix in
`driver_source_loading.spl`: closure traversal now requests only the cached
import vector, rather than reconstructing a four-field result that also carries
the complete source text. Source collection likewise requests only content on
cache hits. This removes the avoidable large-payload return path without
changing discovery, resolution, ordering, aliasing, or invalidation semantics.

The source-shape prevention assertions are in
`test/01_unit/compiler/driver/driver_entry_import_scan_cost_spec.spl`. A post-fix
whole-file timing is intentionally pending: the only available R11 executable
is rejected, embeds the pre-fix driver, fails this workload's HIR correctness,
and cannot publish a warm artifact. Exact after-time/RSS evidence therefore
requires the next admitted bootstrap candidate; quoting a run of the old
embedded driver as an after result would be false evidence.

# Simple versus Go compile-cost attribution — local research

Date: 2026-09-02

## Scope and confidence

This report attributes likely compile-time differences by phase. It does not
claim that Simple is exactly two times slower than Go: no matched clean and
incremental benchmark currently exists. Entries are labelled **measured**,
**observed structure**, or **hypothesis**.

Knowledge routing receipt: feature group `compiler_pipeline`, longest-prefix
layer base `doc/00_llm_process/layer_base/compiler_pipeline/skill.md`; compiler
and driver paths are treated as `mdsoc_only`. Sidecar: N/A; final review uses
the current highest-capability Codex lane.

## Existing evidence

- **Measured:** the global CAS audit measured hashing/inventory of 2,933 files
  at roughly 90–100 ms. This establishes that one bounded filesystem inventory
  is not enough to explain multi-minute builds.
- **Measured:** retained Stage3 memory events show HIR-promotion state growing
  from about 225 MB heap at source index 5 to about 447 MB at source index 168,
  with very large retained-module and validation-key counts. This makes
  semantic/HIR retention a stronger candidate than file virtualization.
- **Measured:** the retained Stage3 attempt did not finish, so there is no valid
  end-to-end clean-build denominator or complete phase profile.
- **Observed structure:** `src/compiler/80.driver/project.spl` still calls
  `list_dir_recursive`; `src/compiler/80.driver/driver_source_loading.spl`
  retains an `rt_dir_walk` route; `src/app/cli/query_check.spl` has workspace
  collection logic. Twenty-one compiler/CLI files mention recursive walk APIs.
- **Observed structure:** `package_module_index.spl`, action keys, typed reverse
  reference receipts, persistent code cache, and host-shared cache policy exist,
  but the package-index plan records production integration as partial and its
  runtime evidence as not run.
- **Observed structure:** full native builds perform specialization, MIR
  lowering/optimization, backend emission, runtime/provider bundling, and link;
  qualification additionally rebuilds fixtures and validates receipts. A tiny
  `check` latency cannot be multiplied by file count to predict this pipeline.

## Ranked likely causes

| Rank | Phase | Current attribution | Basis |
|---:|---|---|---|
| 1 | Semantic/HIR construction and retention | Likely dominant | Measured heap and retained-key growth; package-level early cutoff is not yet proven in production. |
| 2 | Generics and monomorphization | Likely dominant on compiler closure | Stage3 reaches specialization-heavy paths and has failed there; Simple can materialize more concrete work than Go's shape/dictionary sharing. Exact share is unmeasured. |
| 3 | MIR lowering and optimization | Likely large | Every admitted dirty specialization can traverse MIR; current HirType transport investigation is in this path. No complete phase timer exists. |
| 4 | LLVM code generation and optimization | Likely large for release/native | LLVM intentionally trades compile time for optimized output. Cranelift should be measured separately, not averaged with LLVM. |
| 5 | Coarse invalidation / incomplete package archive reuse | Likely large, especially incremental | Persistent package/action/archive integration and exact reverse-dependent scheduling remain partial. |
| 6 | Runtime bundle, provider, stub generation, and linking | Moderate to large for native/bootstrap | Full CLI/bootstrap outputs include runtime/provider work and linking that `check` omits. Relink policy is explicitly part of M4 evidence. |
| 7 | Reverse-reference projection and validation | Moderate; may amplify other phases | Typed receipts exist, but repeated reconstruction or coarse invalidation can expand the work set. Native evidence is blocked. |
| 8 | Cache hashing, admission, and atomic publication | Usually additive; potentially material under disk pressure | One inventory is measured near 0.1 s, but repeated hashing, duplicate caches, fsync, and publication can accumulate. Host storage was recently 99% full. |
| 9 | Source discovery / VFS / virtual-file handling | Additive, unlikely dominant | Recursive scans remain, but the only local scan-scale measurement is ~0.1 s. It becomes important only if repeated per package/request or coupled to cold metadata reads. |
| 10 | SCV snapshot preparation | Intended additive and bounded | Design requires immutable inventory-based snapshots and internal metadata-only writes. Production event routing is incomplete, so cost is unknown. |
| 11 | Qualification | Large wall-time overhead, not compiler core cost | M4/M5 deliberately rebuild, mutate, compare, and retain evidence. Report separately from user-facing compile latency. |

## Virtual-file conclusion

Virtual-file handling is **not currently supported as the dominant explanation**.
The strongest measured local filesystem datum is two orders of magnitude below
the observed multi-minute build scale. VFS/source discovery is an additional
cost and a correctness risk when it recursively scans or rereads unrelated
trees, but the likely primary gap is the amount of semantic, specialization,
MIR, and backend work admitted after discovery. This conclusion must change if
phase tracing shows repeated walks whose cumulative time exceeds 20% of build
wall time.

## Required measurement plan

1. Freeze one immutable SCV revision and use the same source closure, target,
   optimization level, hardware, thermal state, and cold/warm cache definitions.
2. Add nested phase spans with wall time, CPU time, max RSS, bytes read/written,
   file opens, directory operations, and work-item counts for discovery/VFS,
   parse, semantic/HIR, reverse references, specialization, MIR, backend,
   runtime/stub generation, link, cache admission/publication, and SCV.
3. Record LLVM and Cranelift independently. Record qualification outside the
   compiler-core total and also as a separate release total.
4. Run five cases: clean compiler closure, warm no-op, private body edit, public
   interface edit, and foundational package edit. Repeat enough times to report
   median and p95; never mix first-run toolchain startup with warm samples.
5. Emit exact package/SCC work sets and compare them with the expected reverse
   closure. Count unrelated source opens and recursive walks; both must be zero
   on warm and narrow incremental paths.
6. For Go, build a matched package graph and source-byte/AST-node/generic-use
   corpus. Capture `go build -x`, `-debug-actiongraph`, compiler phase timings,
   cache hit/miss state, link time, and `GODEBUG=gocachehash=1` evidence.
7. Attribute the gap using critical-path time, not summed parallel CPU time.
   A phase is dominant only if removing or bypassing it changes matched wall
   time materially.

## Decision thresholds

- If discovery/VFS exceeds 20% of warm or incremental wall time, prioritize the
  persistent index and eliminate repeated walks before backend tuning.
- If dirty package/SCC count exceeds the exact semantic reverse closure, fix
  invalidation before optimizing individual compiler passes.
- If specialization plus MIR exceeds 40%, measure generated function count and
  investigate shape/dictionary sharing and cross-package artifact reuse.
- If LLVM exceeds 40%, use Cranelift for development builds and reserve LLVM for
  release policy, while preserving the selected LLVM+Cranelift architecture.
- If cache publication exceeds 10%, batch hashes/receipts and remove duplicate
  copies without weakening admission or atomicity.

## Local sources

- `doc/01_research/compiler/cache/global_content_addressed_cache_audit_2026-07-24.md`
- `build/bootstrap/stage3/aarch64-apple-darwin/memory-snapshot-v1.52911.events`
- `doc/03_plan/compiler/perf/persistent_package_module_index_compile_optimization_plan_2026-09-02.md`
- `doc/04_architecture/compiler/perf/persistent_package_module_index_compile_optimization.md`
- `doc/05_design/compiler/perf/persistent_package_module_index_compile_optimization.md`
- `build/review/independent_m4_reverse_reference_audit.md`
- `build/review/host_cache_disk_pressure_audit_2026-09-02.md`
- `src/compiler/80.driver/project.spl`
- `src/compiler/80.driver/driver_source_loading.spl`
- `src/compiler/80.driver/cache/package_module_index.spl`
- `src/compiler/80.driver/cache/action_key.spl`
- `src/compiler/80.driver/cache/reverse_reference_receipt.spl`

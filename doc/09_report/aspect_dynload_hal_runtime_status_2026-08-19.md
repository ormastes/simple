# Aspect Dynload, Runtime, HAL, and Bootstrap Status

**Date:** 2026-08-19  
**Refreshed:** 2026-08-19T05:59:06Z  
**Overall:** IMPLEMENTATION ACTIVE; RELEASE NOT READY  
**Plan:** `doc/03_plan/compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md`

This refresh uses retained exact receipts and bounded static inventories. No
broad test suite was run. Counts with different roots or regexes are kept
separate rather than added together.

## Test evidence

### Last exact aggregate (stale after later edits)

`doc/10_metrics/test/current_test_manifest_2026-08-19.sdn` is a bounded,
non-repository-wide manifest. Its last exact aggregate is:

| Dimension | Exact retained count |
|---|---:|
| Manifest rows | 53 |
| Pass rows | 22 |
| Fail rows | 2 |
| Historical-only rows | 7 |
| Not-run rows | 22 |
| Pending-kind rows | 7 |
| Unavailable-kind rows | 1 |
| Ignored-kind rows | 0 |
| Blocker rows | 10 |
| Executed cases | 151 |
| Passed cases | 147 |
| Failed cases | 4 |

The compiler identity for that aggregate is
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
SHA-256 `d3d54fab80199cddb962e07ca1ab655c0cfb8be3594ad4aa615084948116af54`,
stage `unrecorded`, interpreter mode, Linux x86_64, dated 2026-08-19.

The manifest has no skipped-outcome field, so an exact aggregate skip count is
**unavailable**, not zero. An earlier anonymous focused receipt recorded 23
pass, zero fail, zero skip, but it is historical and is not added to the 151.
Likewise, zero ignored rows means only that this bounded manifest contains no
ignored row; it is not a repository-wide ignored-test total.

The 147/4 aggregate is now **stale/pending refresh**. Later fixes and source
edits changed several rows without one new coherent manifest run, so it must
not be described as the current-source pass/fail total.

### Later focused receipts and invalidations

| Focus | Latest retained sequence | Current-source meaning |
|---|---|---|
| `test/01_unit/os/smf/aspect_pack_directory_spec.spl` | 12/13, then 13/13 | Later hardening edits were not rerun; current unknown |
| `test/01_unit/compiler/semantics/facet_static_binding_spec.spl` | 2/5 | Patch and later case expansion were not rerun; current unknown |
| `test/01_unit/compiler/loader/exec_memory_wx_lifecycle_spec.spl` | 6/8 | Two post-receipt fixes were not rerun; current unknown |
| `test/01_unit/os/smf/smf_dynlib_spec.spl` | 1/6 | Latest exact red: five fixtures abort on array-to-int after the three-cycle cap; no native execution; later fix/review in flight and unrerun |
| `test/01_unit/lib/log_level_compat_translation_spec.spl` | 4/7 | Latest exact red: nil length, filtering mismatch, and missing ring record; later source fixes are unadmitted/unrerun |
| CLI focused batch | 7/7 | Final source fixes postdate the receipt; current unknown |
| Database benchmark focused batch | 6/6 | Later exact pass, not folded into the stale aggregate |
| `test/01_unit/lib/io/runtime_alias_semantics_spec.spl` | 5/5 | Exact targeted alias/SCC batch pass |
| Full I/O parity benchmark | unavailable | Native mmap link reproducer passed 1/1; no full benchmark PASS receipt |

The latest exact red receipts forwarded during this refresh are dynSMF 1/6 and
log compatibility 4/7. Both now have later in-flight changes, so final-source
status is unknown. Other named red receipts also predate fixes. None becomes a
pass without a post-fix rerun.

### Ignored-test scope

A separate static source snapshot at `2026-08-19T05:49:09Z` found:

- zero executable Simple `ignore_it(...)` invocations under `test/`;
- two raw Simple `#[ignore]` annotations, the same database test in the
  `test/unit` and `test/01_unit` mirror trees;
- 25 raw non-vendor Rust `#[ignore]` attributes: 16 under Rust test trees and
  nine embedded in Rust source test modules.

These are raw annotation lines, not a deduplicated executed-test receipt.
Therefore the exact repository-wide ignored-test count remains unavailable.
The earlier `8 / 4 / 29` static line figures used broader patterns and are not
comparable to this anchored annotation scan.

## Rust seed and pure-Simple bootstrap

At `2026-08-19T05:50:14Z`, `bin/simple` resolved to
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
with SHA-256
`d3d54fab80199cddb962e07ca1ab655c0cfb8be3594ad4aa615084948116af54`.
It is still the Rust seed authority.

| Stage | Current admitted status |
|---|---|
| Rust seed | Present and deployed |
| Pure-Simple Stage 2 | Absent for the current source/authority |
| Pure-Simple Stage 3 | Absent |
| Pure-Simple Stage 4 | Absent |
| Pure-Simple deploy | Absent |

Historical or stale bootstrap artifacts are diagnostic only. The earlier
statement that a stale Stage 2 artifact could stand in for current admission is
withdrawn. A focused Rust compiler check proves only that seed authority
compiles; it does not admit any pure-Simple stage.

## HAL inventory

The exact static snapshot below was taken at `2026-08-19T05:48:05Z` over the
canonical HAL roots `src/os/kernel/arch`, `src/os/kernel/arch_adapt`,
`src/lib/nogc_sync_mut/hal`, and
`src/compiler_rust/lib/std/src/bare/hal`, excluding every `/vendor/` path.
LOC is physical `wc -l` output.

| Language | Files | LOC |
|---|---:|---:|
| Simple (`.spl`) | 216 | 26,422 |
| C (`.c`) | 22 | 14,747 |
| C headers (`.h`) | 21 | 1,810 |
| Rust (`.rs`) | 0 | 0 |

This is a timestamped volatile snapshot; concurrent policy/bridge files explain
why it differs from the earlier `195/20/16` and `211/22/18` inventories.

## Raw runtime-boundary inventory

### Broad raw `rt_*` lexical surface

At `2026-08-19T05:48:33Z`, a non-vendor scan covered 14,900 Simple files under
`src/`. Declaration lines matched
`^\s*extern\s+fn\s+rt_[a-z0-9_]*\s*\(`. Direct-use lines matched the
`check-no-direct-rt` call-position expression
`^[^#]*\brt_[a-z0-9_]*\s*\(` after declarations were removed. “Owner” means a
path matched the current `no_direct_rt_allowlist.txt`; “leaf” means it did not.

| Raw line-site class | Owner/allowlisted boundary | Non-allowlisted/leaf | Total |
|---|---:|---:|---:|
| `extern fn rt_*` declarations | 980 | 6,480 | 7,460 |
| Direct `rt_*(...)` uses | 1,694 | 11,998 | 13,692 |

The declaration total also partitions by tree as compiler 799, library 3,548,
and other `src/` roots 3,113. These counts include compatibility facades,
runtime/compiler ABI surfaces, test-support source, and legitimate providers;
they are **not** violation counts or a remaining-migration count.

The old 4,277 declaration snapshot (compiler 797; library 3,480) covered only
those two roots at audit start and is non-comparable. The historical 32,061
Rust-tree lexical-token figure and older unpinned 64,335 dirty-tree figure are
also not unique symbols or semantic call sites.

### Authoritative narrow guards

- `direct-env-runtime-guard.shs --working`: PASS, zero forbidden direct
  env/process leaf hooks within guard scope.
- `direct-env-runtime-guard.shs --staged`: PASS, same verdict.
- `runtime_alias_semantics_spec.spl`: 5/5. Its targeted leaves have zero local
  targeted raw externs or broad `io_runtime` imports and preserve the checked
  cwd/process/timeout/env/pid/time/argv semantics plus SCC closure.

These narrow PASS results do not reclassify the broad raw lexical inventory.

## HAL migration and scoped coverage

**Original C files removed or replaced: 0.** Current work consists of policy
extraction slices; retaining the surrounding C acquisition/startup/MMIO ABI
means no whole file may be called migrated yet.

Completed source-extraction slices are:

1. Cosmos FSBL policy;
2. Cortex-M access policy;
3. RV32 boot layout/policy;
4. RV64 PMM;
5. RV64 boot-TCP policy;
6. Cosmos NAND ECC;
7. Cosmos PCIe/NVMe queue policy;
8. Cosmos runtime core, which remains unwired in the production build;
9. Cosmos SMP/GIC policy, with production shared-build wiring present but not
   executed by an admitted Stage-4 compiler;
10. Cosmos MMU/cache policy;
11. Cortex-M scalar/parser/FS policy;
12. Cosmos boot/UART orchestration policy.

RV64 endian/checksum/device-ID remains in flight and is not complete. A Cosmos
merge owner is still integrating the source-complete policy objects, so
source-complete does not mean build-admitted.

Coverage is scoped per slice and **whole-HAL coverage remains unknown**:

| Slice | Exact retained evidence | Limitation/current status |
|---|---|---|
| Cosmos FSBL | Current instrumentation defines 24 outcomes | Not executed with an admitted compiler; the older C 2/2 + Simple 11/11 receipt predates later source |
| Cortex-M access | Static source contract PASS: owner SHA-256 `9f30a5deb1742216c704b48527b1b56fa61ee04a7387c81fa3ed9156aeae849e`; decision inventory SHA-256 `58d0b54b3e6dcc73ef98e772c18d3791a32cb28e781751b81453a95690e2ea4c`; 8 pinned decisions / deterministic 16 branch outcomes; 2 header-backed C ABI exports / 6 admitted object globals | Actual compiler/runtime branch execution is blocked pending admitted Stage 4. The 39-row/78-outcome parity, access objects, and AN505 8/8 QEMU receipt used Rust seed SHA-256 `d3d54fab80199cddb962e07ca1ab655c0cfb8be3594ad4aa615084948116af54` and are diagnostic only. Combined images remain stale until parser/FS integration refreshes them. |
| RV32 boot policy | Source extraction present | Coverage gate fails closed with `missing=8` |
| RV64 PMM | Actual C/gcov 20/20 | QEMU not run |
| RV64 boot-TCP | Source extraction present | No current coverage/admission receipt retained |
| Cosmos NAND ECC | C bridge 4/4 | Mixed C+Simple execution blocked |
| Cosmos PCIe/NVMe | C 16/16 and Simple 15/15 reported | QEMU blocked |
| Cosmos runtime core | Source extraction present | Production build unwired |
| Cosmos SMP/GIC | 24 functions; frozen C oracle 234 rows and LLVM 34/34 branches; source counter pins the same 17 decisions/34 outcomes | C/source gate PASS; admitted Simple parity/object/unit/ARM link remains blocked before execution; production wiring present but unexecuted |
| Cosmos MMU/cache | 22 exports, 37 decisions; C contract/oracle PASS 2,829; ARM C import closure PASS | Native Simple/unit/ARM link blocked without Stage 4 |
| Cortex-M scalar/parser/FS | 10 exports, 22 pinned decisions; diagnostic spec 4/4 with exact interpreter C parity | Official Stage 4 gate blocked; actual 44/44 coverage, ABI objects, and three combined-board links unavailable/stale |
| Cosmos boot/UART | 15 scalar exports; 279-row independent C parity inventory; 38 named semantic predicates / 76 Simple outcomes; frozen oracle 34 LLVM sites / 68 edges, with all 68 edges hit by the C-only diagnostic | Production extraction/wiring and object-admission source contracts are present; only the C diagnostic executed. Admitted Simple parity/unit/object/link receipt remains blocked without Stage 4, and no board result is claimed |

No host semantic matrix, object-format gate, build-only wrapper, or QEMU smoke
can be blended into physical-board evidence or a whole-HAL percentage. The
retained zero-file/zero-branch “100%” receipt remains invalid.

The four RISC-V evidence producers now share a fail-closed evidence contract:
RV32 boot layout, RV64 boot-TCP, RV64 freestanding policy, and RV64 PMM all
require an explicit current-tree Stage 4 binary/provenance pair and atomically
publish provenance- and runtime-bound receipts. Freestanding additionally
binds the RISC-V cross compiler. This hardening does not create a PASS receipt:
the runtime gates and QEMU were not run. The freestanding decision audit's raw
owner-source pin was refreshed from the current source; its compiler-emitted
named-row pin remains runtime-gated. Operator details are in
`doc/07_guide/os/riscv_hal_migration_evidence.md`.

## Remaining features and runtime hooks

- Refresh the bounded manifest after final source edits; rerun aspect directory,
  facet static binding, W^X lifecycle, legacy log, and CLI focused specs once.
- Complete startup config cutover, loader-policy consumption, component
  resolver production cutover, and final CLI help/router cutover evidence.
- Repair and rerun the real admitted-byte dynSMF loader: its source check is
  green, but the focused runtime spec is 1/6 and no native execution exists.
- Prove current aspect-pack admission and wire the currently inert production
  hooks: `forbidden_io_checker`, windowed pack I/O/index cache, joinpoint slots
  and advice registry, startup/manual activation, unload/pin driver, and the
  operational-seal scheduler/publication seam.
- Deliver the typed facet compiler surface or retain its explicit blocker.
- Complete the remaining in-flight HAL policy slices and refresh combined-image,
  mixed-language, QEMU, and physical-board gates without widening evidence.
- Produce admitted current Stage 2, Stage 3, Stage 4, deployment, essential-tool,
  performance, and full I/O parity receipts.
- Run the Class-A harness v2 full matrix. Its schema/source is complete and the
  selftest passes exactly 18 negative controls. Its current receipt root is
  `build/perf/startup_class_a_v2/`, but current preflight exits 2 because Stage
  4 is unavailable; there is no matrix receipt or PASS.

The targeted runtime alias/SCC batch is closed at 5/5; this does not close the
repository-wide runtime-boundary migration.

## Worktree, JJ, and process cleanup

- Nine safe `/tmp` worktrees were removed non-force after individual checks.
- `rescue/restart12-qemu-matrix-20260819` preserves
  `b215137faaa078a496792653c807fa6422a7e9f3`.
- `rescue/restart12-qemu-matrix-preaudit-20260819` preserves
  `de3c16b6da56cc9f32f8225784290f22d9df8dba`.
- The restart12 JJ workspace was retained because it has an unpublished
  26-file payload and a conflicted `main` bookmark.
- `/tmp/simple-fix-tty-signal-boundary` was retained: non-force removal refused
  even though normalized diffs were empty.
- `/tmp/jjtest`, a standalone toy JJ workspace, was retained. No JJ workspace
  was removed.
- The latest cleanup pass killed no Codex or Claude process; no stale such
  process was identified, and only current root session groups remained.
- No bulk branch/worktree/JJ deletion is authorized. Retained lanes still need
  their own reachability, cleanliness, process-CWD, lock, and payload checks.

## Current verdict

**STATUS: FAIL.** The last aggregate is stale, multiple post-fix focused rows
remain unrun, the full I/O parity benchmark is unavailable, no current
pure-Simple Stage 2/3/4/deploy chain exists, zero C files have been fully
migrated, whole-HAL coverage is unknown, and several production hooks remain
unwired. In-flight source work is not counted complete.

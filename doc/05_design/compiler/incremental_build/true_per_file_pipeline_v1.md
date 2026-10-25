# True per-file pipeline v1 — one job per source file, src → parse → HIR → MIR → obj, no phase barrier

**Status:** FIXED design (2026-10-25, release/1.0.0 @ `b9fd03115ad`). Owner: Fable lead;
implementers listed in §6. Supersedes nothing: it is the execution contract for
rule 1 of `src_based_tldr_build_v1.md` ("per-file jobs, no stage barrier") and
§8/§9 of `build_runner_fiber_scheduler_v1.md`, written against what the code
does TODAY (measured, see §1).

## 1. What is NOT per-file today (measured on the frozen Windows stage2, 2026-10-25)

| Claim | Reality |
|---|---|
| #4525/#4547 "per-file src→obj default" | Only the whole-program MIR shortcut was replaced by per-module lowering. Phases are still global barriers: parse ALL → surfaces ALL → HIR ALL → mono ALL → MIR → objects. No object exists before the last HIR finishes. |
| HIR shards | Never admitted: `[hir-cache] disabled reason=no-compiler-scope` — `SIMPLE_FRONTEND_CACHE_SCOPE` is never published (gate at `driver_source_pipeline_parsing.spl:962` + children spawned before any publish), and under the default explicit-semantic-policy lane the closure digest is forced to `""` (`driver_hir_pipeline_lowering.spl:1087`). With the scope set by hand (probe run2) 4 shards lowered 307/308 modules in parallel. |
| MIR shards | `claims=0`, fall back to in-process MIR: they need the HIR inventory the HIR shards never produced. |
| Per-module cost | 1453 modules × ~1.4-1.8 s single-threaded (stage3: 2566 s loop + 425 s post-loop + 414 s mono). Of a module's 1.4 s only ~0.05-0.3 s is HIR lowering proper; the rest is re-parse, validation-blob encode, O(n²) admission, progress I/O. |
| Frontend `.fpc` cache hit | 455 ms/file vs 130 ms cold parse (pure-Simple sha256 + flat-pool replay). A hit is slower than parsing. |

## 2. Contract

**Unit of work = one source file F. Job J(F):**

```
read F → parse F (full AST) → publish TLDR(F) (set-once, temp+rename)
      → resolve imports of F lazily: TLDR/skeleton SURFACE of each imported module
        (shared immutable table, single-flight; produced by parsing the skeleton,
        never the bodies, of the dependency — never by waiting for "all parsed")
      → HIR(F) → mono(F) (module-scoped, §4) → MIR(F) → obj(F) (+ receipt)
```

- Jobs run `threads` wide (80 on the dev host) under memory admission; a job
  never waits for a global phase. The parent (orchestrator) does: source-closure
  scan → run the job pool → link. The parent parses and lowers NOTHING.
- Cross-module information comes only from TLDR/surface data of the imported
  modules (forward declarations). A missing TLDR is produced by the job that
  needs it (or awaited from the job that owns that file) — single-flight.
- Every artifact (TLDR, surface skeleton, HIR cache entry, object, receipt) is
  published by temp file + atomic rename; freshness is content identity.
- Receipts carry monotonic timestamps `parse_done`, `hir_done`, `mir_done`,
  `obj_done`. **Acceptance proof:** on a small closure, exists (A, B) with
  `obj_done(A) < hir_start(B)`.

## 3. Execution unit: worker PROCESSES with a claim loop (v1), fibers later

In-process fibers cannot run two parses concurrently yet (frontend parse state
is process-global, tracker item 32). v1 therefore uses long-lived worker
processes: each worker claims one file from ONE ledger, runs the whole J(F),
publishes obj + receipt, claims the next. This merges today's separate
`--hir-shard` and `--mir-shard` passes (and their barrier) into one
`--file-worker` role; the ledger, claim/terminal/seal records, memory admission
(`shard_threads_mem_cap`) and the link-only final worker
(`SIMPLE_MIR_SHARD_LINK`) are reused unchanged. In-process FileFiber
(`file_fiber_v1.spl`) replaces the process pool once item 32 lands; the
contract above does not change.

## 4. Module-scoped monomorphization (no global mono pass)

A worker instantiates every generic call site it lowers for F into F's own
object: mangled `template$<type-args>` symbols emitted as COMDAT/linkonce_odr so
duplicates across objects dedupe at link. Template modules emit no instances.
Inference uses the TLDR signature of the template (`generic_tldr_view_table_v1`,
`.rr` usage refs) and the template body from the owner's TLDR/AST on demand.
This removes the 414 s global mono pass and the "specialization placed in the
template's module" coupling. Design detail: `build_runner_fiber_scheduler_v1.md` §8.

## 5. What the worker must NOT do

- Parse the whole closure for surfaces (today every shard child re-parses all
  1453 files, 130 ms each, which is why shards are memory-capped at 12).
  Surfaces of imports come from TLDR `surface` sections / skeleton parses
  (`driver_hir_worker_surface_v1.spl`, `module_surface_skeleton_v1`), cached.
- Encode a HIR validation blob per module (85 % refused, decoded again later).
- Depend on `SIMPLE_FRONTEND_CACHE_SCOPE` being set by someone else: the
  orchestrator publishes one cache identity before spawning anything.

## 6. Work packages (parallel worktrees off release/1.0.0, PR each)

**Superseded 2026-10-25 (status column below):** verified against
`origin/release/1.0.0`. P0 DONE #4565 `700a2f742a4`. P1 DONE #4566
`ae96dd0bb6e` (staged codegen batch default 8, not 1). P2 DONE #4557
`4ce52b4d99f` + #4562 `5e8ad7e3638` (lazy validation blobs). P3 DONE (opt-in)
#4576 `106ab239fff`, #4584, #4585, #4588 (P-A), #4594 (P-E planner + object
cache). P4 DONE (opt-in) #4575, #4580, #4597 (P-B), #4598 (P-G3, no global
mono pass on this lane), #4603 (P-D). P5 PARTIAL — #4585/#4588 limit HIR to the
claimed module's import closure; TLDR specialization list + `.rr` producers (P-G2) DONE
#4600 `73c4aef632a`. P6 OPEN — ParseContext item 32 at stage 2 (#4502, #4568). Default
flip (P-F #4592 `1c6ccfb61c4`) is prepared but **not flipped**:
`NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "0"` in
`src/compiler/80.driver/driver_build/native_file_worker_v1.spl:45`; enable with
`SIMPLE_FILE_WORKERS=1`. The §2 overlap proof (`obj_done(A) < hir_start(B)`) has
a checker (`scripts/check/check-per-file-overlap-receipt.shs`) but **no native
receipt yet**; §7's limit still holds.

| # | Package | Owner | Status |
|---|---|---|---|
| P0 | Cache identity published before spawn; explicit-policy lane gets a digest; HIR cache decoupled from `.fpc` on/off | WP-A agent | PR in progress |
| P1 | Object emitted right after each module's MIR (`SIMPLE_NATIVE_STAGED_CODEGEN_BATCH` default 1 on the file-worker lane) | MIR→obj streaming agent | spec sent |
| P2 | Post-loop O(n²) admission; validation blob encode off | landed #4557; blob PR in progress | |
| P3 | `--file-worker` claim loop: HIR→mono(F)→MIR→obj per claimed module in one worker, parent = closure scan + pool + link only | new agent | brief issued |
| P4 | Module-scoped mono with COMDAT emission | new agent | brief issued |
| P5 | Import surfaces from TLDR/skeleton only (retire whole-closure parse in workers) | after P3 | planned |
| P6 | In-process FileFiber once item 32 lands | scheduler agent | planned |
| P-G4..P-G6 | Template body loader, specialization list from mono instances, instance build plan in pool | per-file agents | DONE #4625 #4628 #4653 #4672 |
| P-H | Stage3 + plain native-build through file-worker pool, fail-closed | per-file agent | DONE #4683 `bf4c14a31e1` |
| P-G7 | Instance object producer + link wiring | per-file agent | PR #4696 OPEN, approved by lead reviewer (comment), pending merge |

## 7. Honest limits

Nothing in this document is verifiable until a stage2 built from these sources
exists; the frozen stage2 that produced §1's numbers predates every fix. The
seed cannot interpret the current stdlib on Windows (parse error in
`windows_redirected_process.spl`), so specs are landed on gates only until a
Linux/updated-seed run confirms them.

### Progress 2026-10-25 (evening)

PR states verified with `gh pr view` against base `release/1.0.0`.

**Per-file packages merged:** P-A #4588 `e0efb59638f`, P-B #4597 `7ec523277de`,
P-C #4589 `d1ee8738d60`, P-D #4603 `cbe361c2497`, P-E #4594 `9314979e6e6`,
P-F #4592 `1c6ccfb61c4`, P-G1 #4591 `3383735e8cb`, P-G2 #4600 `73c4aef632a`,
P-G3 #4598 `220b35b4b35`, P-G4 #4625 `7ec28192eb0`, P-G5 #4628 `963f32429a3`,
P-G5b #4653 `5de3687be0b`, P-G6 #4672 `03e6d90af24`, P-H #4683 `bf4c14a31e1`
(stage3 and plain native-build go through the file-worker pool, fail-closed).
E-MONO-040 fails closed for imported generics: #4651 `6c257d14918`.

**Open:** P-G7 #4696 (instance object producer + link wiring) is OPEN; approved by lead
reviewer (comment), pending merge. Merge release_phase3 into
release/1.0.0: #4704 OPEN.

**Default stays off:** `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "0"`
(`SIMPLE_FILE_WORKERS` default "0"). Flip waits on a proof run: stage3 -> stage3'
built with P-H, then a per-file self-rebuild that yields an overlap receipt
(`scripts/check/check-per-file-overlap-receipt.shs`). No such receipt exists yet.

**Stage evidence (in progress, not a retained measurement):** stage2 built cold
from `d72188e68ec` (1534 modules, 0 failed, mswsock workaround dropped). The
stage3 whole-program run is in progress with 0 MIR errors (was 3211); it is
single-threaded and CPU-bound.

**Other landings:** #4610 stale lock reclaim / orphan reaping `52ecd8b7725`;
#4622 Mach-O as conditional build tag `a269ecaecba`; #4623 pre-push gate clear
error for missing gate script `fc894af98af`; #4633 host-scaled tree RSS cap
`ae3c1307476`; #4682 llvm-mingw drive-letter admission `784ac5aa304`; seed
externs #4608 `57a129fb2b9` and #4688 `5bd6f027abb`; spec fixes #4636
`1cfdf5876ca`, #4635 `33bfd461fbb`, #4638 `4f5e0d91b88`. Also merged since the
morning: memory #4698 `574b8bb6e70` and #4705 `31bafe03f9e` (HIR / per-module MIR
eviction), perf #4693 `35fe920618d` (sha256 accelerator), MIR #4706
`a853ac75861`, stage2 #4684 `dd7cede08a3` and #4697 `7c1e83a584b`.

**Still failing / under investigation:** HIR cache selfcheck (239/1495 hits);
seed JIT fallback on `native_build_main`.

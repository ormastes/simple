# Stage 3 no-GC parse/HIR retention exceeds bootstrap memory budget

Date: 2026-08-25

Status: OPEN — measured bootstrap blocker; no source workaround is safe.

## Impact

A self-hosted Stage 3 bootstrap in dynload mode retains memory approximately
linearly through parsing and HIR lowering until it crosses the host memory
budget. The process was terminated during HIR rather than reaching the Stage 3
candidate/admission boundary. This blocks the required self-host compiler
evidence and, consequently, MC/DC and RT/HAL runtime verification.

This is not a stall: the compiler remained CPU-active and the build progress
counter advanced throughout every sample below.

## Measured evidence

Run artifacts, retained in the worktree:

- Progress telemetry:
  `build/bootstrap/mcdc-postfix-stage3.progress.log`
- Native compiler phase log:
  `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`

The progress watcher measured the complete bootstrap process tree. The active
compiler was the admitted Stage 2 Pure Simple executable, with two compiler
threads; there was one substantial `simple` process, so the reported tree RSS
is not a sum of parallel parse workers.

| Phase/progress | Tree RSS | Observation |
| --- | ---: | --- |
| source closure complete (715 files) | 1.21 GiB | fixed compiler/closure baseline |
| parse 353/715 | 5.33 GiB | active, CPU about 100% |
| parse 693/715 | 10.10 GiB | active, CPU about 100% |
| HIR 51 | 12.10 GiB | continued growth after parse |
| HIR 58 | 13.03 GiB | process terminated before Stage 3 completed |

The parse-only increment from the source-closure baseline is roughly 8.89 GiB
at 693 modules, or approximately 13 MiB/module. This contradicts the older
1.53 MiB/module parse slope recorded for a different bootstrap measurement in
`memory_retention_compiler_and_interpreter_2026-08-21.md`; that older result
must not be used to predict this Stage 3 lane.

## Narrow source-level suspect

The Stage 3 invocation takes the plain full-program parse path. In
`src/compiler/80.driver/driver_source_pipeline_parsing.spl`:

- Lines 938–1000 retain every `ParserModule` in `parsed_modules` while all
  `self.ctx.sources` remain live.
- Lines 1001–1004 additionally retain path/content/tag/DAG arrays for the
  project-wide layer-call check. In particular, `layer_wiring_contents` stores
  every `source.content` again logically (the dominant cost is expected to be
  parsed module/flat-pool state rather than these source bytes alone).
- The plain loop does not invoke `driver_end_transient_parse_scope()` after
  each module, unlike selected entry/streaming paths.

This sits on a no-GC runtime. `CompileContext.evict_sources()` and related
reference-dropping operations cannot reclaim the retained class-backed module
objects: `src/compiler/80.driver/driver_types.spl:1157–1172` documents the
measured zero-reclaim behavior and why unsafe deep free would corrupt aliased
objects. Therefore adding a local free/drop call is not a safe mitigation.

HIR then compounds the retained front-end footprint. Historical snapshot
evidence in
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/memory-snapshot-v1.*.events`
also shows monotonic live-heap/RSS growth while module/HIR collections increase;
it is supporting context, not substituted for the current-run measurements
above.

## Reproduction

Run an admitted Stage 3 bootstrap in the same mode, retaining its progress and
native-build logs. Conceptually:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --stop-after-stage3 --mode=dynload --jobs=half \
  --output=build/bootstrap \
  --progress=build/bootstrap/mcdc-postfix-stage3.progress.log
```

Use the planner/admission receipt required by the bootstrap workflow. Do not
substitute a Rust seed, reduce the source closure, or treat a lower-memory
parse-shard helper as evidence: this bug is specifically the full Stage 3
self-host compiler lane.

## Safety constraints

- Preserve full-program diagnostics, module ordering, layer-call validation,
  and source-span behavior.
- Do not free ParserModule, HIR, flat-pool, source, or environment objects via
  untyped/deep runtime frees; aliasing is known and can cause use-after-free.
- Keep the solution Pure Simple. C/Rust replacement is not an acceptable
  resolution.
- Any streaming/promotion design must maintain deterministic parent-authority
  commit and prove that later HIR/MIR consumers cannot access evicted state.

## Acceptance criteria

1. The same full dynload Stage 3 command completes and publishes a valid Stage
   3 candidate/provenance receipt.
2. Telemetry records peak tree RSS and per-phase progress for the run.
3. Parse RSS growth is bounded with a stated, measured per-module budget, and
   HIR lowering does not exceed the documented host/bootstrap memory budget.
4. Full-program layer-call validation and diagnostics remain equivalent on
   positive and intentionally-invalid fixtures.
5. A focused regression test proves no later phase dereferences evicted
   parser/flat-pool/source state; a correctness test covers the chosen
   streaming or ownership boundary.
6. The fix is measured against this baseline once, including elapsed time and
   peak process-tree RSS; any residual memory limit is recorded rather than
   hidden by lower parallelism or a smaller source set.

## Cycle 15 evidence and converged repair (2026-08-26)

Cycle 15 reached streaming HIR with 717 surfaces and 996 visited source
identities. The direct simple-tail repair changed `native_build_help` from Cycle
14's `has=false stmts=1` to `has=true stmts=0`; `run_rt_native_build` formed as
`has=true stmts=11`. The preserved log ended at line 11666 while lowering entry
function index 13, `native_build_entry_from_args`, before its `formed` receipt.
Repeated malformed tail-span receipts (three in the final preserved sequence)
immediately preceded SIGSEGV. Cycle 14 had
formed that recursive if/elif function as `has=false stmts=1` and continued.
No preserved core or backtrace was available.

Because the crash occurred before this function's `formed` receipt and hence
before its publication, the evidence exonerates publication for this specific
failure. It does not prove the exact faulting instruction. The strongest
inference is a pre-publication complex-control tail boundary, consistent with a
returned `HirExpr`/`kind` reconstruction after simple branch tails and with the
repeated malformed-span receipts. The
accepted repair is the destination-owner design in the paired architecture and
detail-design documents. Falling back to old HirStmt transport is containment
only because it restores missing returns. Rewriting branch values into Return
is rejected.

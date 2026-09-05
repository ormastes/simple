# Compiler Driver Layer Expert

Mission-critical V2 bootstrap/admission status is owned by
`doc/03_plan/sys_test/mission_critical_infra_hardening_v2.md`; its active owner
failure is `doc/08_tracking/bug/stage3_selfhost_exit_139_2026-08-14.md`.

## Role

Own source discovery, import closure, phase orchestration, execution-mode
selection, and compiler-driver performance under `src/compiler/80.driver/`.

## Source-loading invariant

- `Check` mode loads only the requested checking scope.
- `Interpret` mode keeps the explicit entry bounded and lets the interpreter
  module loader resolve imports lazily.
- Native entry-closure mode loads the transitive closure selected by
  `SIMPLE_NATIVE_BUILD_ENTRY` and suppresses whole-project bulk loading.
- The entry-closure collector excludes documentation fixtures beneath `/doc/`,
  but must retain explicitly imported executable modules under `src/app/doc/`.
  The regression is `driver_source_loading_spec.spl`'s application-doc closure
  case; do not broaden the exception to arbitrary documentation trees.
- Other project compilation modes may bulk-load the self-hosted compiler roots
  where their global compilation model requires it.

## Formal Verification 2.0 invariant

`CompileContext` retains `AssuranceStrictnessV2.Verified` while frozen V1
consumers conservatively project it to `critical`. A `verified` compilation
must not lower string-only direct calls and then claim a closed MIR/VIR path.
Until the frontend captures resolver `SymbolId` decisions and finalizes
`ResolvedDirectCallManifestV1` after complete MIR construction,
`CompilerDriver.lower_to_mir` must fail with
`FV2-E-CALL-MANIFEST-PRODUCER`. Do not weaken this to a name lookup or bypass
it with a bootstrap/entry-closure path; runtime and generated calls require an
explicit external-boundary model.

Do not reuse the native-only entry-closure environment flag as a shortcut for
interpretation: downstream HIR/MIR branches attach native/bootstrap semantics
to it. Keep the interpret exclusion explicit in
`driver_source_pipeline_loading.spl`.

## Performance evidence

The compiler-loader negative-cache and packed-byte performance handoff lives at
`doc/03_plan/sys_test/compiler_loader_script_crosslang_perf.md` (plan content
accepted; operational reconciliation pending; feature verification blocked).
Preserve its
distinction between facade failed-existence probes and filesystem syscalls, its
caller-sensitive cache key and reset generation, and its admitted-self-hosted
evidence rule. Live feature verification remains blocked by two distinct
prerequisites: the older deployed candidate's wrapper/help admission segfault,
and historical lane-A Stage3 context corruption after a clean 603-file parse.
Fresh r3 remains unproved: its first process was intentionally stopped before
Stage 2 admission so review corrections could be source-frozen; partial output
is not authority and no verdict/cycle was consumed. The latter is tracked at
`doc/08_tracking/bug/build11_stage3_compile_context_corruption_2026-08-14.md`.

For a one-file interpreted entry, measure wall time and max RSS through the
normal `bin/simple` command. A run that never reaches user code is source-loader
cost, not workload cost. Preserve the normal CPU guard; raising it is diagnostic
only and cannot be passing evidence.

Focused contract:
`test/01_unit/compiler/driver/interpret_lazy_project_sources_spec.spl`.
MCP end-to-end witness:
`test/02_integration/app/mcp_stdio_integration_spec.spl`.

Typed-storage native codegen freezes deep-copied module-qualified evidence
before cache lookup. The parent then creates class-handle MIR+storage capsules;
the builder callback sees only the frozen batch and module name. Revalidate
complete MIR/storage identity before and after codegen, bind object bytes and
size in the result receipt, and publish cache checkpoints only through the
parent completion hook. Do not call this real concurrency: the current
builder branch batches sequentially, and process workers need a complete codec.

## Separate RV64 Stage 3 MIR receiver corruption handoff (2026-08-14)

This is not the Build11 compiler-loader frontier above. The RV64 prerequisite
bootstrap reaches HIR with zero errors, then its
Stage 3 log ends in MIR method-call lowering with an impossible receiver local
ID. Inspect `method_calls_literals.spl` receiver resolution/writeback and the
`value_struct_layout.spl` push-heavy caller shapes. Do not claim the direct
`CompileContext.error_count_value` reads fixed the root cause; require an exact
native reproducer, adjacent aggregate/method-call regression, and a fresh
Stage 4 essential-tools receipt. Tracking:
`doc/08_tracking/bug/stage3_selfhost_post_hir_segfault_2026-08-14.md`.
## Restart12 bootstrap/deployment status (2026-08-14)

The current Stage 2 compiler is bootstrap-only. The static-owner receiver
frontier is repaired; a later GDB run proved the next Stage 3 exit 139 at
aggregate `HirType` transport from `maybe_copy_array_value` into
`remember_local_hir_type`. Keep that metadata owner-local and cross the helper
boundary with scalar source/destination IDs. The focused native regression is
green, but Stage 3/4 remain unadmitted, so do not advertise SPipe, deployment,
or release admission. Current owner and resume condition:
`doc/08_tracking/bug/stage3_post_file_copy_exit139_2026-08-14.md` and the
canonical deployment plan.

Phase-1 source loading owns closure COMPLETENESS, and its line cursor mixes
units: `text.len()`/`text[a:b]` are byte-indexed, `char_code_at` is
char-indexed. `_driver_line_end` now returns a `(byte, char)` pair and both of
its callers advance both cursors together; do not reintroduce a single cursor.
A truncated closure does not fail here — it fails much later in HIR as
`unresolved type`, attributed to the wrong file. Verify closure size at
`[build] source_closure N/N` before believing any HIR error attribution.
See `doc/08_tracking/bug/simpleos_wm_vulkan_cross_arch_rows_blocked_2026-08-31.md`.

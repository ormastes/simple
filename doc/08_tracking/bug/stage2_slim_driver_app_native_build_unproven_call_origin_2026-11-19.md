# Stage-2 slim driver: app native-build closures hit unproven-call-origin AOT gate

Date: 2026-11-19
Host: Windows 11, x86_64-pc-windows-msvc
Driver: stage-2 compiler built from pinned 41ea2084e43b (bootstrap lane c42s2,
slim bootstrap surface, commands: compile + native-build only)
Tree: .build/mcp-release-v7-source @ 41ea2084e43

## Observation

`native-build` of `src/app/devhub/main.spl` fails deterministically with 11
codegen ICEs of one class — the AOT call-origin provenance gate:

```
AOT compile error in <module>: unproven-call-origin: MIR call target lacks
proven source/runtime/foreign origin: callee=<fn> fn=<caller> module=<module>
```

Affected modules (all in the app-IO/stdlib surface):
- lib.common.text_bytes (callee str_len)
- lib.common.encoding.host_text_boundary_v1
- lib.common.crypto.sha256, lib.common.crypto.sha256_core (callees rotr32/shr32/add_mod32)
- lib.nogc_sync_mut.sffi.fs (callee text_byte_buffer)
- lib.nogc_sync_mut.sffi.process_capture, process_environment_capture
- lib.nogc_sync_mut.io.external_file, external_text_io, windows_process_owner, windows_process_text

286 modules fail in aggregate; link blocked.

## Reproduced with BOTH command shapes

1. Bare: `native-build src/app/devhub/main.spl -o ... --cache-dir ...`
   (modules resolved via SCV snapshot)
2. Canonical: `native-build --source src/compiler --source src/app --source src/lib
   --entry-closure --entry src/app/devhub/main.spl --output ...`
   (modules from worktree sources)

Identical 11 ICEs either way → not a snapshot-path artifact. The callees
(str_len, rotr32, text_byte_buffer, process_capture_text_data_v1, …) are
ordinary source functions in the same closure.

## Contrast

The same driver family builds the MCP closure fine (mcp-c41: 396/396 surface,
387/387 objects, deployed + smoke PASS). The MCP closure simply never includes
the sffi/fs/crypto/encoding surface the devhub closure pulls in.

Stage-2's own build (1579 modules, seed-driven) and the slim verification
matrix ("in-process native-build" driven by the verification harness with its
own provenance context) also pass these modules — so the gate failure is
specific to plain CLI native-build of the app closure under the slim driver.

## Assessment

P2, toolset-shaped, not source-shaped: no individual source file is wrong
(HIR lowering succeeds for all 4001 modules in the full-cli verification; the
gate trips at AOT codegen). The route for devhub/caret/cs native binaries is
the stage-4 full toolset (expected to carry the provenance/trust context the
harness sets in-process). Revisit after the c43 stage-4 lands; if the stage-4
CLI hits the same gate, escalate to P1 and instrument the origin-proof pass.

Evidence: build/ice/8496_*/ice_receipt.tsv and build/ice/15296_*/ice_receipt.tsv
in the v7 lane tree; logs build/nb/devhub-build.log, devhub-build2.log.

## Update 2026-11-20: export-list hypothesis disproved; minimal 2-module repro

Status: open (no fix landed; root cause narrowed, not proven).

Linux lane, frozen Stage 2 `/home/dev/xc/simple-p2` (ubuntu-p2), x86_64 linux
`native-build --entry-closure`, fixtures under `~/simple/build/callorigin_fx`
(sources: `C:/dev/wt/xc-wsl-scripts/callorigin/fx/`):

| fixture | callee decl | result |
|---|---|---|
| `exponly/main.spl` -> `exponly.core.ex_len` | `fn ex_len` + `export ex_len` | ICE `unproven-call-origin callee=exponly.core.ex_len` |
| `pubonly/main.spl` -> `pubonly.core.pb_len` | `pub fn pb_len` | ICE `unproven-call-origin callee=pubonly.core.pb_len` |
| `tb_main.spl` -> `std.common.text_bytes` | (stdlib) | ICE in `lib.common.text_bytes` (`str_len`) and `tb_main` |

So `pub` vs export-list visibility is NOT the discriminator: a trivial
two-module cross-module call from a fresh module fails. Adding `pub` to
`string_core.str_len` would not fix anything.

xcmatrix census (`~/log/xm`, linux-x64/a64 + win-x64 lint/test), distinct
Unknown callees: `text_bytes.text_byte_buffer` (51), `string_core.str_len` (28),
`encoding.external_text.external_text` (18), `crypto.word_ops.rotr32` (16),
`sffi.fs.file_open` (14), `traceability.case_events.test_failure_code_name` (12),
`text_bytes.text_to_bytes` (12), `traceability.model.trace_text_order` (8).
6 of 8 are `pub`. Callers like `text_bytes.text_byte_buffer` cascade from a
provider module that itself failed.

Source reading (pure-Simple compiler, release/1.0.0):
- `provider_callable_call_origin_v1` (`50.mir/_MirLowering/provider_metadata.spl`)
  answers Source only when `callable_text_value_abi` has the provider row; no
  visibility gate anywhere on registration or HIR import binding.
- The declaration-provider prescan (`prescan_module_declarations_v1` ->
  `prescan_declaration_callables_v1`, `declaration_providers_v1.spl`) has had
  **no caller** since `ab9305d783e` (40.mono removal deleted the MIR archive
  consumer that installed `declaration_repository` and ran it). Rows now come
  only from `prescan_module_struct_names` over `ctx.hir_modules`
  (`driver_pipeline_lowering.spl`). Leading hypothesis: in the per-file worker
  unit, the provider's HirModule is not in `ctx.hir_modules` (only the owned
  module), so its callable rows are never registered. Next step: trace
  `ctx.hir_modules` keys in a file-worker MIR unit (`SIMPLE_COMPILER_TRACE=1`)
  for the `pubonly` fixture, then a spec asserting
  `provider_callable_call_origin_v1 == Source` for an A->B call.

## Update 2026-11-20 (b): root cause proven; fix landed for review

Status: verification-pending

Discriminating experiments (frozen Stage 2 `/home/dev/xc/simple-p2`, `pubonly`):

| run | result |
|---|---|
| `--threads 1` dynload (in-process serial lane) | PASS, 0 ICE |
| `--threads 1` one-binary | PASS, 0 ICE |
| `--threads 12` dynload (per-file worker pool) | FAIL, `callee=pubonly.core.pb_len` |
| `--threads 12` + `SIMPLE_UNIT_TLDR_IMPORTS=0` | PASS, 0 ICE |

The failing unit logs `[unit-tldr] ... summaries=1` and
`[file-worker] mir-child hir closure modules=1 of=2`: the PM3 unit lane
(d98bf2d99e1, 2026-10-27) resolves imports through TLDR summary surfaces and
loads HIR only for its targets, so `prescan_module_struct_names` never visits
the provider and `callable_text_value_abi` has no row -> `MirCallOrigin.Unknown`.
ab9305d783e (2026-10-31) removed the declaration-provider prescan that could
have covered this, but did not trigger it.

Workaround: `SIMPLE_UNIT_TLDR_IMPORTS=0` (or `--threads 1`).

Fix: `MirLowering.register_surface_callable_origins_v1`
(`50.mir/_MirLowering/provider_metadata.spl`) fills absent origin rows from a
surface's `is_extern` flag (Source / Foreign; free functions only; never
overrides HIR rows; link names untouched). The driver's MIR setup
(`driver_pipeline_lowering.spl`, after struct prescan, unit-scoped only) feeds
every surface whose module has no HIR. Spec:
`test/01_unit/compiler/50.mir/surface_only_provider_call_origin_spec.spl`
(5/5; RED 0/5 without the method). Native verification pending a Stage 2
rebuild: re-run the `pubonly` fixture sharded and run the binary (link-name
parity of the fallback callee name is the residual risk).

## Update 2026-11-20 (c): #10534 step never fired natively; lifetime fix

Status: verification-pending

Native verification of #10534 (Stage 2 from release/1.0.0 6d8ca1e90d30) still
failed `callee=lib.common.string_core.str_len`, with zero
`surface_call_origins` lines. Cause: `lower_and_check_retained_owner_impl`
(`driver_hir_pipeline_lowering.spl`) releases the surfaces
(`streaming_surface_owner_ready = false`) at the end of HIR lowering, BEFORE
MIR setup, so the #10534 gate was always false. Fix: capture flat rows
(`driver_surface_call_origin_rows_v1.spl`) into
`CompilerDriver.surface_call_origin_rows_v1` just before the release (only when
worker HIR loads are restricted); MIR setup consumes them and prints
`[mir-setup] surface-call-origins rows=<n> candidates=<m>` unconditionally.
Spec: `test/01_unit/compiler/80.driver/surface_call_origin_rows_lifetime_spec.spl`
(4/4; ordering assertion fails on the #10534 tree). Native: rebuild Stage 2,
re-run `pubonly --threads 12`, expect the `[mir-setup] surface-call-origins`
line and rc=0.

## Update 2026-11-20 (d): struct layouts — unit imports hold interface-only HIR

Status: verification-pending

After #10575 (`surface-call-origins rows=84`) the lint lane failed next on
`missing exact struct construction layout 'HostTextByteSpanV1'`. Native repro on
the frozen Stage 2 (fixture `structimp`: imported struct + enum + struct return,
`--threads 12`): `missing exact struct construction layout 'SiSpan'`,
`mir-child hir closure modules=1 of=2`; wall 5:04, peak RSS 3.16 GB (baseline).

Cause: the TLDR unit lane holds no provider HIR, and every MIR prescan table
(struct/class layouts, enum inventory, call origin, fn return/param HirTypes, RTI)
is filled only from held HIR. Fix: in unit mode an import row the unit does not own
loads the provider's cached HIR interface-only (`hir_module_interface_only_v1`)
into `ctx.hir_modules`; never lowered or claimed; a cache miss keeps the old
behaviour. Log: `[unit-tldr] import interface-hir loads=<n>`.

Spec: `test/01_unit/compiler/80.driver/unit_import_interface_hir_spec.spl` (4/4;
driver assertion RED without the change). Native verification and per-worker
RSS/time cost need a Stage 2 built from this branch.

Revision (Opus review FAIL on the first cut): an importing unit cannot rebuild the
provider's cache key (its closure digest covers its own surfaces + TLDR imports),
and the summary row's identity is the stub's. The provider now publishes
`{queue}/{sha256(path)}.hirkey` (key + parser binding, atomic) after a cache
store/hit; the importer loads interface-only through it and logs
`[unit-tldr] import interface-hir hit|miss`. `driver_mir_owner_disposition_v1`
returns placeholder for any non-target row of a scoped unit, so held interface or
closure HIR is never fed to MIR. Status stays verification-pending (native proof
by the coordinator after a Stage 2 rebuild).

Update 2026-11-21 (e): native proof of #10594 on Stage 2 a61dff89cc0 removed the
HostTextByteSpanV1 error, but logged hit=107 / miss=18698. 18.3k of those misses were
rows the unit never imports: the loop tried every frozen row outside the load closure
(25 units x ~722 rows). Real import rows across the run: 422 summary-bound. The lookup
now runs only for TLDR summary-bound rows. It also waits, up to
SIMPLE_UNIT_IMPORT_IFACE_WAIT_MS (default 60000), for a provider that is in flight
(claimed, no terminal, no sidecar yet). It never waits for an unclaimed or finished
provider. The new first error, FILE-WORKER-E-CLOSURE-INCOMPLETE for io/dir_ops.spl,
comes from the phase-2 surface readiness check
(driver_source_parse_streaming.spl:600), which runs before any #10594 code. It is
not caused by #10594. Status: verification-pending.

Update 2026-11-21 (f): the dir_ops FILE-WORKER-E-CLOSURE-INCOMPLETE is a real gap
in the PM3 unit plan. dir_ops imports std.io_runtime, which re-exports with
`export a, b from nogc_sync_mut.io_runtime`, and tldr_route_import_specs_v1 dropped
that form. As a result the origin module (and
nogc_async_mut.sosix.host_facade) was never summarized or parsed, its row stayed
unbuilt, and the phase-2 readiness walk failed the target. It is neither a stale
summary nor 83499674f1b: io_runtime.spl and dir_ops.spl are unchanged since 11-13.
The lane only reaches this unit now. Fix: scan `export ... from ...`.
Spec: test/01_unit/compiler/80.driver/tldr_route_export_from_spec.spl (3/3; red before).
tldr_route_spec's 7 failures are pre-existing and the same set with or without the fix.
Status: verification-pending.

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

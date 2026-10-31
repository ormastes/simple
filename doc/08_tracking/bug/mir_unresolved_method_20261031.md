# mir-unresolved-method-20261031: pinned-stage2 MIR gaps across 25 full-CLI modules

Date: 2026-10-31. Status: OPEN.

Found by: phase-1 full-CLI build (entry `src/app/cli/main.spl`) with the pinned
phase-1 compiler at `build/devhub-goal/runtime-authority/simple`; the MIR stage
failed on 25 modules (~90 fatal errors).

## Failure class

The pinned stage2 MIR lowering cannot resolve a family of receiver/shape
combinations that HIR accepts. All are compiler limitations, not source bugs;
workarounds are behavior-preserving source changes, tagged at each site:

    # @workaround bug=mir-unresolved-method-20261031 reason=<shape>; <what was done>

Sub-classes seen (with the per-class canonical bug docs they overlap):

1. `unresolved method call: <m>` on receivers whose MIR type is unknown —
   notably locals bound from generic `List.get()` results (index access
   `xs[i]` keeps the type), chained/direct call-result receivers in some
   positions, and other inferred bindings. Overlaps:
   `methods_mir_2026-10-31.md`, `mir_unresolved_method_inferred_receiver_2026-10-24.md`.
2. `B5b: match ...` — match-subject typing gaps; bind the subject to an
   explicitly typed local before the match. Overlaps:
   `hir_generic_enum_self_match` family (PR #5635).
3. `undefined variable` / `E-RTI-004: symbol ...` — missing/incomplete import
   or qualification that pinned stage2 needs spelt out (mono-era base, later
   compilers resolved transitively).
4. `for-in over ...` unsupported shapes — rewrite as index loops. Overlaps:
   `stage2_mir_for_in_unsupported_shapes_2026-10-10.md`.
5. `unsupported Result ...` — Result-typed expressions in positions the
   pinned MIR cannot lower; restructure into typed locals or explicit
   Ok/Err handling.

## Worked-around modules

All 25 modules from the phase-1 full-CLI failure list were worked or
analysed; per-module status is in the commit body. Summary of patterns:

- Enum-payload / match-expression / unsafe-block / unwrap bindings lose
  their receiver type in library-mode MIR lowering: rebind to an
  explicitly typed local or annotate the binding (`val x: T = ...`).
  (data_ops via spreadsheet.spl, cmd_wiki, env_access_host,
  file_ops, process_ops, io_runtime, compile_targets, wm_access_cli,
  tldr_function_header_v1, update/main, database/test, db_atomic)
- `len` on `List<T>.get(i)` results: use index access `xs[i]`, which keeps
  the element type (debug_ui).
- `for-in` over bindings with lost types: rebind to a typed local first
  (update/main, database/test).
- `B5b: match has multiple wildcard/binding default arms`: val-constant
  match subjects become binding arms — rewrite as an if/elif equality
  chain; duplicate wildcard arms drop the unreachable ones
  (wm_access_cli, validation).
- `unwrap()`/`unwrap_or`/`?` on Results with scalar or array payloads:
  rewrite as explicit `Ok/Err` matches (real_device_readiness, deflate,
  db_atomic).
- Missing methods that modern toolchains compile leniently
  (`rt_function_not_found` WARN+nil): define the intended method
  (spreadsheet.spl hide_row/unhide_row/unhide_all_rows — the
  `is_row_hidden` precedent) or rewrite against the API that actually
  exists (word_app rich-text calls).
- `sort_by` with a lambda comparator: explicit index-loop sort by the
  same total order (lint_code).
- `parse_float` alias missing from the pinned MIR builtin table: use
  `to_float` from the same erased-receiver family (duplicate_check
  config).
- `async fn main` desugar references an unresolvable `Future`: body had
  no awaits, so a plain `fn main` is equivalent (tools/fix main).
- `text.from_bytes` static receiver unresolvable: use the sanctioned
  `common.text_bytes.bytes_to_text` provider (provider_cli entry).

## NOT fixed (with reasons)

- app.build.submodule_cli (1): reported error is an operator-overload
  failure naming `CodegenParamsV1` from compiler/70.backend, which the
  module neither imports nor references; no span; appears to be a
  mono-instantiation attribution artifact. No source site in the module.
- app.ui.access_cli (16) and lib.nogc_sync_mut.io.file_text_session (8):
  `E-RTI-004` interface-row generation failures. These rows are only
  emitted under `native-build --mode dynload`; the mandated single-file
  `compile --format=smf` verification (entry or dependency mode) cannot
  reproduce them, and the reported symbols (`DbValue::as_int`, `format`)
  are not referenced by the modules' own code — a pinned-stage2 RTI
  walker gap on imported symbols, not a fixable source shape.
- compiler.hir.archive.tldr_function_header_v1 (1 of 2): the
  `operator overload for struct HirInterpolation` error has no span and
  names a struct the module does not reference (same mono-attribution
  family as submodule_cli). The `len` site at 179:24 was fixed.

## Removal condition

Retire (revert the tagged workarounds) when a stage2 that resolves these
shapes bootstraps and compiles the full CLI without them.

## Round-4 addendum (2026-10-31, dynload full-CLI gate)

Second-pass census from the phase-1 full-CLI build at head 080b8d0ba7a
(same pinned compiler, entry src/app/cli/main.spl, --mode dynload): 29
modules / ~230 fatal errors. All new sites tagged with the same
`bug=mir-unresolved-method-20261031` marker; the round-4 commit body lists
per-module status. New shapes worked around in round 4:

- E-RTI-004 'X is not a nominal type with a defining module' on non-pub
  methods/fns referenced through dynload interface rows: visibility
  widening to `pub` at the declaring module (tldr_table_v1, io/types
  is_would_block, sffi/dynamic DynLib raw-call pair, database/sql/types
  DbValue/DbRow impl methods, database/checker check_* fns). All are
  behavior-preserving visibility-only changes.
- E-MIR-TYPE-TypeParam unsubstituted 'T' at every
  `Future.from_value(...)` call in lib.nogc_async_mut.io.buffer/tcp:
  pinned MIR lowers the generic callee body with T unsubstituted even
  with explicit call-site type args; worked around by constructing the
  `Future(state: [], poll_result: Poll.Ready(v))` record directly
  (identical to from_value's own body).
- 'tuple index 0 is out of range for a 0-element tuple': bare `-> tuple`
  return annotations erased the arity; spelled the tuple types at the
  three parse helpers in lib.editor.backend.gui_backend.
- 'unsupported Result unwrap payload type' (scalar payload):
  unwrap() -> tagged Ok/Err match helpers in
  os.drivers.nvme.nvme_performance_contract.
- 'enum match expression and retained Result/Optional declarations
  conflict': Option-typed vals initialized from match expressions
  rewritten as var + if-val / statement-arm matches
  (compiler.semantics.resolve); unannotated Optional match subjects
  annotated (app.mcp_t32.dialog_tools).
- E-RTI-007 'declared return is Any; not representable in an interface
  row' on tuples containing the erased element type `list`: retyped the
  callee and inlined the header-attach helper
  (app.devhub.adapter_outlook).
- Dynload-only `len`/`parse_i64`/`set_prop` receiver-type losses:
  same round-1..3 rebind/index/annotation patterns at the new sites
  (formula, access_controller, wm_access_cli, llvm_target,
  frontend_parse_cache, zip, semver_old, environment_variant_policy_
  sources_v1 with Result.Ok/Result.Err qualification).

Still not fixed from earlier rounds: app.build.submodule_cli and
compiler.hir.archive.tldr_function_header_v1 (operator-overload errors
naming structs the modules do not reference; no span; mono-attribution
artifact — see NOT fixed above).

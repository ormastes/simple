# Stage 2 sanity panic: transient retained parser ownership (declaration promote)

Date: 2026-10-22
Status: root cause fixed at the runtime layer (`rt_transient_heap_promote`);
stage 2 sanity re-run is the pending verification.

## Observed failure

Stage 2 bootstrap on release_phase3 (aarch64-unknown-linux-gnu, LLVM 23.1.2).
After fixing the `rt_io_file_open` ABI regression (see
`native_file_open_text_arity_schema_vacuity_2026-10-21.md` update), the sanity
p2_add frontend probe crashed in the retained parse scope:

```
transient retained parser ownership failed for .../scv-snapshots/.../p2_add.spl
[hir-shard] owner=0/1@0 status=CRASH exit=-134 (SIGABRT)
```

Temporary driver diagnostics (removed after use) narrowed the AND-chain in
`driver_promote_retained_frontend_owners_v1`
(`src/compiler/80.driver/driver_source_pipeline_parsing.spl:285`) to:

```
registry=true parser=true declaration=false resource=true cache=true shared=true coverage=true
```

## Root cause

`parser_declaration_metadata_promote_transient_owner`
(`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:840`) promotes
`UNSAFE_ANNOTATIONS`, `ENUM_ATTRIBUTES`, `ENUM_OPEN_REGIONS` through
`rt_transient_heap_promote`. `driver_end_transient_parse_scope` resets those
module globals to fresh process-immortal arrays after every file. A source with
no enum/annotation content (p2_add.spl) therefore promotes an EMPTY IMMORTAL
array: `rt_core_transient_classify` returns class 0 (not transient-owned), and
the runtime's no-op-success exemption only covered registered immortal heap
STRINGS (added 2026-09-25 for the Windows stage-2 HIR-memo case), not arrays.
`ok = root_class == 1 && ...` went false, the AND-chain failed, and the driver
panicked.

## Fix

`src/runtime/runtime_native.c::rt_transient_heap_promote`: the class-0
registered-immortal exemption now accepts ANY registered immortal object kind,
not only `RT_VALUE_HEAP_STRING`. Promotion of an already-persistent owner is a
no-op success by definition; unregistered heap pointers still fail closed.

## Verification

Pending: full `--full-bootstrap --stop-after-stage2` re-run (runtime archive
rebuilds via `runtime/build.rs` rerun-if-changed on the edited `.c`).

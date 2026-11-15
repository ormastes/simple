# FILE-WORKER-E-CLOSURE-INCOMPLETE on every Linux cross build (unit TLDR alias row)

- **Status:** verification-pending
- **Severity:** P0 (all four `xc_new.sh` linux-{x86_64,aarch64} {lint,test} builds)
- **Builder:** phase-2 `~/xc/simple-p2` (sha256 `fcf9ad14…14f6`, from `1139820f170`)

## Symptom
`FILE-WORKER-E-CLOSURE-INCOMPLETE: import-closure surface missing for
.../src/lib/common/text_bytes.spl` (or `string_core.spl`), then "native-build
worker exited with code 1" / "MIR shard aggregate failure". With
`SIMPLE_COMPILER_TRACE=1`: `phase2:surface:missing-direct-edge kind=import
source=text_bytes target=string_core` (and the reverse; the two files import
each other).

## Root cause
Per-file unit lane (PM3, `SIMPLE_UNIT_TLDR_IMPORTS` default on) binds each
non-picked import to a TLDR summary surface. Two key mismatches across the
`lib.*` / `std.*` alias rows of a `src/lib` file (the closure loader admits the
canonical `lib.*` name first; `std.*` twin is conditional):

1. `driver_unit_tldr_imports_v1.spl` `unit_tldr_plan_v1`: the import spelling
   `std.common.string_core` was looked up only verbatim in `module_paths`;
   on a miss the module was skipped (no summary, no fallback parse).
2. `driver_source_parse_streaming.spl:331-334`: the summary surface was looked
   up by the ROW's module name (`lib.common.string_core`) while the plan named
   it by the import spelling, so the first row fell to the placeholder parse
   and the `std.*` alias row hit the alias branch — never marked built.

Either way `worker_built` stayed false, `worker_surface_ready_v1` refused the
target, and the worker failed closed.

Not caused by PR #9427 (closure digest): readiness reads only `worker_built`
and canonical paths. `SIMPLE_HIR_SHARDING=0` "refuses" because the file-worker
pool fails closed with no in-process fallback
(`src/app/cli/native_build_main.spl` `run_file_worker_pool_v1`,
`hir_disabled_by` -> `file_worker_pool_refusal_v1`).

## Fix
`unit_tldr_module_path_for_v1` (std. -> lib. fallback) and
`unit_tldr_surface_for_row_v1` (name, then canonical path). Spec:
`test/01_unit/compiler/80.driver/unit_tldr_alias_row_binding_spec.spl`.

Workaround until a rebuilt phase 2: `SIMPLE_UNIT_TLDR_IMPORTS=0` (verified: the
x86_64 lint repro passes phase 2 with 0 CLOSURE-INCOMPLETE and reaches
native_compile).

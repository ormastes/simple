# `@export("C", name: ...)` ignored under `--no-mangle`

Status: **RESOLVED 2026-08-17** (compiler export-name fix landed; the earlier
provider workaround is no longer load-bearing).

## RESOLVED — root cause and fix

Root cause: the pure-Simple LLVM backend chose symbol names in
`MirToLlvm.llvm_function_symbol_name`
(`src/compiler/70.backend/backend/_MirToLlvm/class_def.spl`), which handled the
`main` entry contract, `no_mangle`, and runtime-owned-name collisions — but
**never consulted `MirFunction.export_name`**. The `name:` argument was parsed
(`00.common/_Attributes/decl_attrs.spl:parse_export_attrs`), lowered onto HIR
and carried all the way through MIR, and then simply never read on the LLVM
path; only the C backend's `derive_export_name` used it. Under `--no-mangle`
the function returned the bare MIR name, so `nm -D` showed
`pure_simple_provider_query_v1` instead of the requested
`simple_provider_query_v1`.

Fix: `translate_module` (`_MirToLlvm/core_codegen.spl`) records every
non-empty `MirFunction.export_name` into a new
`MirToLlvm.export_symbol_names` map, in the same pre-pass that already records
runtime-owned-name collisions (it must run before any function is emitted,
since a call site can be translated before its callee's definition).
`llvm_function_symbol_name` then treats a requested name as **authoritative in
both mangling modes**, with the single exception of the `main` entry-point
symbol contract, which still wins.

### Verification (2026-08-17)

The fix is pure-Simple source, which `bin/simple` reads on every run, so no
rebuild was needed. A direct probe exercising exactly the two specs' assertions
via `bin/simple run` reports **6 of 6 PASS**: the incident pair resolves to
`simple_provider_query_v1` under `no_mangle`, a non-exported name passes through
unchanged, the requested name also wins in default mangle mode, siblings are
untouched, and `main` still resolves to `__simple_main`. Before the fix the
`export_symbol_names` field did not exist at all, so both specs were red on
their first line.

`bin/simple test` was not usable as evidence for these two specs — it was killed
by the CPU monitor (rc=143) and, on the run that completed, emitted no results
line (the known silent-green defect). Per `.claude/rules/testing.md` that is
INCONCLUSIVE, hence the direct `run` repro above.

Specs (repro + generalization, mirror-synced into `test/unit/`):
- `test/01_unit/compiler/backend/export_c_custom_name_spec.spl` — the exact
  incident pair under `no_mangle`, plus non-exported passthrough.
- `test/01_unit/compiler/backend/export_c_custom_name_general_spec.spl` —
  requested name honoured in default mangle mode, applied per-function with
  siblings untouched, and the `main` contract not overridden.

The admitted Stage 2 compiler successfully built the Pure Simple provider
archive, but `nm -D` on the linked shared object exposed
`pure_simple_provider_query_v1` and `pure_simple_cli_command_invoke_v1` instead
of the requested `simple_provider_query_v1` and
`simple_cli_command_invoke_v1` names.

Provider fix: declare the two functions with their exact ABI symbol names and
retain `@export("C")` plus `--no-mangle`. This is deterministic and avoids a
linker alias shim. The compiler should separately make the `name:` attribute
authoritative under no-mangle builds.

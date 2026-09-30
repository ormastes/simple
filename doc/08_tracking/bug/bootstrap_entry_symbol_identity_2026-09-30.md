# F11: bootstrap function bodies can borrow a local extern's symbol

Status: SOURCE-ONLY FIX DRAFT. All added specs and fixtures are UNEXECUTED.
No build, probe, runtime test, debugger session, or performance measurement was
run for this task. Publication and producer admission require separate review.

## Scope and provenance

- Isolated lane: `D:/wk-extern-entry-binding-20260930`.
- Base: `fd82119d9c911b2cecaa66d95d16930792a40953`, the locally available
  `origin/main` at lane creation. The coordinator reports subsequent a52e313
  contains a test-only change; this lane does not claim to be based on a52e313.
- One production change: `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl`.
- Ownership check found no other active owner of this declaration identity cause.
- Historical producer SHA-256:
  `9088595d5a51191f9895293c8d6c8c17ddefe4d6e12dbf04015b705372b02308`.
- Original report remains unchanged at
  `D:/wk-scv-split-perf-20260930/doc/08_tracking/bug/native_local_extern_rebinds_entry_function_2026-09-30.md`.

The historical evidence is under
`/mnt/simple-bootstrap-6b2/scv-cold-inventory-perf-20260930/probe/`:
`local-extern-recursion-reproducer.spl`, `extern-binding-evidence.json`,
`original-entry-disassembly.txt`, `final-entry-disassembly.txt`, and the prior
`failed-run-*` debugger receipts. No new inspection of runtime memory occurred.
The original disassembly bound calls at 0x40237d and 0x40238d back to
0x4022e0 (`__simple_main`). A later facade variant instead defined the entry
body as `rt_heap_registry_count` and failed to link `__simple_main`.

## Static cause

1. `SymbolTable.new` starts an ordinary allocating table. It does not reserve
   the legacy bootstrap IDs.
2. `_Items/module_build.spl` predeclares all parsed functions, including externs,
   with `symbols.define`, carrying their declared signatures. Externs retain
   their bare runtime names. Bodies are then lowered from these declarations.
3. `lower_function(ParserFunction)` formerly bypassed that table for eight
   known bootstrap names. `main` received synthetic ID 6, `bootstrap_version`
   ID 1, etc. Neither assignment reserved or populated that table row.
4. Identifier/call lowering uses the real declaration table. Consequently,
   a row allocated to an extern can also be attached to the entry body.
5. MIR's `provider_callable_symbol_name` resolves a function ID through the
   table and uses that row's stored name/link metadata. `function_lowering`
   passes that result to `begin_function`. Provider callable registration also
   derives lookup keys from the row. A wrong body ID can thus redirect call
   linkage or give the entry body an extern's name.

The identity contradiction is directly established in source. The historical
producer's exact table allocation order was not recorded, so attributing each
historical instruction to a particular row is an inference, not a new runtime
reproduction. No extern-filter/index mismatch was found: the flat AST count,
function-at, and declaration-at accessors traverse the same function-tagged
declaration sequence, and the HIR accumulator stores complete HirFunctions.

## Narrow repair

All parsed function bodies now use the existing qualified name lookup-or-define
path. A predeclared function retains its allocated ID and signature. A missing
declaration gets a real table row. Existing method/static qualification and
the explicit nil guard are preserved. No allocator reservation, call ABI,
function order, or entry export rule changes.

## Fixed-ID consumer audit

Full-tree `git grep` was used, including paths outside the sparse checkout.

| Surface | Finding and disposition |
| --- | --- |
| `bootstrap_function_symbol_id` | No occurrence in base source or tests. |
| HIR `bootstrap_hir_symbol_for_name` | Used by legacy direct-flat lowering and two expression fallbacks; retained. |
| HIR `lower_bootstrap_flat_function(decl_idx)` | No call sites found; fixed-ID behavior retained. |
| Flat expression identifiers and `bootstrap_flat_var_expr` | Both prefer a successful real symbol lookup over synthetic fallback. |
| MIR `bootstrap_mir_symbol_for_index` | Declaration only, no callers found; retained. |
| Driver `bootstrap_symbol_for_name` | Declaration only, no callers found; retained. |
| MIR `lower_bootstrap_flat_function(symbol, name, body)` | Takes its ID from caller; separate overload, unchanged. |
| LLVM entry selection | `llvm_function_symbol_name` uses name `main` and entry-module flag to emit `__simple_main`; does not require ID 6. |
| Known builtin dispatch | `is_bootstrap_builtin_fn` remains name based; its handling/signatures are unchanged. |
| Literal ID 6 tests | Existing borrow, OpenCL, symbol-index, and mono fixtures use arbitrary IDs; no entry-ID contract found. |
| `bootstrap_post_entry_lowering_source_spec.spl` | Already expects absent text `if not bootstrap_hir_symbol_known_name(name):` in the base. This pre-existing source-shape assertion was not modified or run. |

Interpreter comparison: `src/app/interpreter/module/evaluator.spl` registers
extern declarations by name in `extern_functions`; `call/dispatch.spl` checks
extern ownership by callee name before ordinary function lookup. This source
path does not use the native fixed entry-ID mapping. No interpreter execution
or claim about deployed interpreter completeness is made.

## Release/1.0 applicability (read-only)

Inspected local `origin/release/1.0` at
`d921e11599ee94519c9813c4df0ab1ed6e391d70`. The same identity defect is present:

- `declaration_lowering.spl:246-247` overrides actual declaration lookup with
  `bootstrap_hir_symbol_for_name(fn_.name)` for known names.
- `lowering_helpers.spl:490` maps main to 6 and bootstrap_version to 1.
- `hir_types.spl:269` initializes `next_symbol_id` to zero.
- `module_build.spl:368` allocates bootstrap declarations through `define`.
- Backend `_MirToLlvm/class_def.spl:178` selects main linkage by name.

Therefore propose the same narrow lookup-authority repair for release/1.0
after the main fix is reviewed and validated. Release lacks the modern MIR
provider-name helper, so identical downstream symptoms are not claimed. Its
declaration API also differs (the older predeclaration uses a boolean visibility
argument); regression tests must be adapted to that API before validation.
No release branch or worktree was modified and no release test was executed.

## Prevention coverage and remaining validation

`test/01_unit/compiler/hir/bootstrap_entry_symbol_identity_spec.spl` parses real
declarations, predeclares them in an explicit order, and calls the real HIR and
MIR lowerers. The deliberate allocator prefix makes extern row 6 deterministic
without relying on dictionary ordering. Assertions check every body ID and
stored name, main's MIR name, scalar call target identity, distinct main/extern
IDs, scalar/text extern return shapes, and empty lowering error lists. The
known-name case also checks that a call to `bootstrap_version` uses its allocated
body ID. An explicit assertion on `ambient_bootstrap_enabled()` prevents these
cases from passing by silently exercising only the normal lowering mode.

Six UNEXECUTED cases cover zero externs, one before/after main, two before main,
mixed ordering, and a second known name (`bootstrap_version`) allocated at row
8 rather than synthetic row 1. The zero-extern case allocates main at row 7.

Two native fixtures under `test/fixtures/native_extern_entry_identity/` retain
the real runtime extern names with declarations before or after main. They do
not require exact allocation counts or monotonic heap growth. Future validation
must first inspect objects: main's executable body defines `__simple_main`,
the runtime externs are imports, and neither call targets the entry. Only after
that gate should the fixtures execute and return zero.

This task intentionally performs no test execution, so parser/typecheck/runtime
validity of the new tests remains unverified. Compiler/core and MCP smoke gates
remain outstanding. No release, merge, producer admission, or performance claim
is authorized by this draft.

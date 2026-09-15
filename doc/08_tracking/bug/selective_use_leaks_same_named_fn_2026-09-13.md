# Selective `use m.{a}` leaks m's same-named functions over the importer's own

- **Date:** 2026-09-13
- **Component:** interpreter / module name resolution
- **Binary:** `bin/release/x86_64-pc-windows-msvc/simple.exe` (Rust seed), `run`
- **Severity:** high — wrong function silently called; can die with rc 0 and no output

## Symptom

`std.nogc_sync_mut.http_client/request.spl` defines its own
`fn http_get(url) -> (text, text, list, text)`. After adding
`use std.nogc_sync_mut.io.http_sffi.{http_request_raw}` to that file, calls to
`http_get` resolved to `io.http_sffi.http_get`, which returns an
`SffiHttpResponse` object. A spec calling `request_add_header(http_get(url), ...)`
failed with `semantic: invalid operation: tuple index access on non-tuple type object`.
Only `http_request_raw` was named in the import list.

## Minimal repro (three files in one directory)

`leak_provider.spl`
```
class Obj:
    code: i64

fn http_get(url: text) -> Obj:
    Obj(code: 7)

fn helper() -> i64:
    42
```

`leak_consumer.spl`
```
use leak_provider.{helper}

fn http_get(url: text) -> (text, text):
    ("GET", url)

fn build() -> (text, text):
    http_get("x")
```

`leak_main2.spl`
```
use leak_consumer.{http_get}

fn main():
    val r = http_get("y")
    print "method={r.0} url={r.1}"

main()
```

| run | expected | actual |
|---|---|---|
| `simple run leak_main2.spl` | `method=GET url=y` | `method=nil url=nil` (provider's `Obj` came back) |
| same, calling `build()` inside the consumer | `method=GET url=x` | no output at all, rc 0 |
| control: delete `use leak_provider.{helper}` | `method=GET url=y` | `method=GET url=y` |

The only difference in the control is the selective import that names
`helper`, never `http_get`.

## Expected

A selective import binds only the listed names. A module's own top-level
definition always wins over anything a `use` brings in, and names that are not
listed must not become visible at all.

## Workaround in tree

`send_request` now lives in `src/lib/nogc_sync_mut/http_client/transport.spl`,
which defines no `http_*` builder names, so importing `io.http_sffi` there has
nothing to shadow. `request.spl` no longer imports `io.http_sffi`. Pinned by
`test/01_unit/lib/nogc_sync_mut/http_client/header_shim_spec.spl`, which calls
`http_get` through the root shim.

Related: the root shim's earlier `add_header as request_add_header` alias
resolved back onto the shim's own `add_header` and recursed forever. That is
likely the same resolution defect seen through an alias.

## Fixed in the Rust seed (2026-09-14), pending redeploy

**Root cause.** Module flattening tags every free function with its owning
module (`FLATTEN_MODULE_OWNER_ATTR_PREFIX`, `tag_function_module_owner`) and
each `use` leaves a decodable `__simple_flatten_import_binding__` marker
const, but nothing in `Lowerer::lower_identifier`
(`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`) ever consulted
either. A bare callee name was resolved purely by looking it up in
`self.module.functions` / `self.globals` by TEXT, so whichever module's
same-named definition was processed last in the flattened unit silently won
for every OTHER module's calls to that name too — the selective import of
`helper` was irrelevant; the leak came from flattening merging `http_get`
from both modules into one namespace with no owner-aware lookup at the one
call site that resolves identifiers to callables.

**Fix.** `Lowerer` now tracks, per flattened unit: `flatten_fn_owners` (every
function name -> the owner of each definition, so a collision is
detectable), `flatten_owner_import_bindings` (decoded from every import
marker, keyed by importer), and `current_function_owner` (the owner of the
function whose body is currently being lowered). A colliding function
definition is lowered under an owner-mangled symbol
(`flatten_emitted_symbol`) unless it is the entry module's (or, absent an
entry-module definition, the module last in flattening order) — same
last-write-wins bare name it always had, kept only as the historical
non-colliding fallback target. `resolve_flatten_owned_callable` then answers,
for a bare name referenced from the function being lowered: (1) does the
CURRENT module define a colliding `name` -> use its own symbol; (2) does the
current module import `name` (via a decoded marker, alias or not) -> use the
exact owner+name the marker names; (3) is `name` a function alias of a
colliding name -> use a definition from a module other than the importer
(the `fn f(): g()` recursion trap). **The load-bearing wiring is in
`lower_identifier` itself** (`expr/mod.rs`, new branch right after the
`ctx.lookup` local-variable check, before the existing import-alias branch):
it calls `resolve_flatten_owned_callable` and, on a hit, emits
`HirExprKind::Global` under the resolved owner-exact symbol with that
symbol's own type. An earlier draft of this fix only patched
`calls.rs`'s return-type inference to consult the owner resolver — that
never touched the actual call-target symbol `lower_identifier` already
picked, so the draft's own regression test kept failing
(`consumer's build() must call the consumer's own http_get`) until the fix
was moved to `lower_identifier`. Once the symbol is right there,
`call_return_type`'s own `self.module.types.get(fallback)` fast path already
returns the correct return type, so no separate return-type patch is needed
in `calls.rs`. `calls.rs` still needed one companion fix: the
`proven_nonescaping_functions` check there must test the RESOLVED symbol
(`func_hir.kind`), not the bare `callee` text — that set is keyed by
`flatten_emitted_symbol`(module_pass.rs) same as `globals`, so a
bare-name lookup there has the identical collision hazard as the identifier
lookup did.

**Files:**
`src/compiler_rust/compiler/src/hir/lower/lowerer.rs` (new state +
`flatten_owner_of`, `flatten_is_collision`, `flatten_owner_defines`,
`flatten_emitted_symbol`, `resolve_flatten_owned_callable`),
`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs` (`lower_identifier`
wiring — the actual fix), `src/compiler_rust/compiler/src/hir/lower/expr/calls.rs`
(`proven_nonescaping_functions` keyed by resolved symbol),
`src/compiler_rust/compiler/src/hir/lower/module_lowering/function.rs`
(track `current_function_owner` across a function body, emit under
`flatten_emitted_symbol`), `src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs`
(register function signatures/`pure_functions`/`proven_nonescaping_functions`
under the same emitted symbol).

**Tests:** two new cases in
`src/compiler_rust/compiler/src/mir/lower/tests/seed_regression_tests.rs`:
`selective_import_does_not_override_importers_same_named_function` (this
bug's exact shape — provider placed last so a bare last-write-wins pick
would still fail) and `import_alias_of_colliding_name_does_not_bind_importers_own_function`
(the `add_header as req_add_header` self-recursion trap from the "Related"
note above). Both pass; the full `hir::lower::` test module (300 tests) and
`mir::lower::tests::seed_regression_tests::` (39 tests) are green on this
change; one pre-existing unrelated failure
(`mir::lower::tests::branch_coverage::expr::result_helpers_lower_to_builtin_enum_ops`)
reproduces identically with the fix reverted, so it is not a regression from
this change.

**Known remaining gap, not fixed here:** `check_contract_purity`
(`calls.rs`) still calls `self.is_pure_function(name)` with the bare
identifier text for CTR-030/031/032 purity checks in contract expressions
(`in:`/`out:`/`invariant:`). `pure_functions` is populated under the same
owner-mangled `flatten_emitted_symbol` as everything else here, so a
contract expression naming a colliding function could get a false
pure/impure verdict in the same collision shape as this bug, just for a
diagnostic rather than the call target. Left unfixed pending an owner
context at that call site (contract expressions are lowered without the
enclosing function's `current_function_owner` threaded through in the same
way); flag if hit in practice.

**Pending:** deploy (this is the Rust seed, bootstrap-only — the fix ships
to `bin/simple` on the next bootstrap redeploy, not immediately).

## Pure-Simple compiler (`src/compiler/**`) checked separately — bug class does NOT apply

Selective imports are resolved in
`src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl`,
`resolve_import_symbols` (line 247). For a selective `use m.{helper}`
(`item_start != item_end`), the loop at lines 386-393 registers **only the
explicitly named items** via `register_imported_symbol` — it never walks any
of `m`'s other functions. That whole-module walk
(`register_glob_imported_symbols[_depth]`, lines 67-245) only runs for a glob
import (`use m.*`, `item_start == item_end`), where pulling in everything is
the correct semantics. So there is no "flatten every function from an
imported module into one namespace" step for a selective import in this
implementation, and consequently no leak-via-an-unrelated-function path: the
Rust seed's bug came specifically from flattening merging modules' full
function sets before resolution; the pure-Simple resolver never does that
for `use m.{name}`.

`register_imported_symbol_inner`
(`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:449-487`)
does write function symbols into `HirSymbolTable.define`
(`src/compiler/20.hir/hir_types.spl:348`) last-write-wins by bare name (that
file's own comment: "Function symbols are not first-write-wins") — but the
only way to reach that overwrite is a genuine, narrower case: the importer's
own function has the *same name as a symbol it explicitly imports*, an
expected, self-inflicted collision, not this bug's "importing one name drags
in an unrelated same-named function" shape. This resolution path is
load-bearing (core HIR import registration, invoked from ordinary module
lowering), not dead/unused code. No fix needed here.

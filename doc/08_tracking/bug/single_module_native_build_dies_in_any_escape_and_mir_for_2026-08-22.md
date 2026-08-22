# Single-module `native-build` dies before codegen — two stacked defects

- **Filed:** 2026-08-22
- **Status:** defect 1 FIXED; defect 2 OPEN (blocks both lanes below)
- **Impact:** every single-file / single-module `native-build` (the deploy
  gate's shape) and the **engine-differential native lane**
  (`scripts/check/check_engine_differential.spl`), which reported
  `LANE_ERROR ... native-build produced no artifact` for all 13 fixtures.

Both were found with `SIMPLE_DEBUG_FIELD_ACCESS=1` (wired by `f7586d7eff3`),
which prints the receiver, the expression and the full call stack for a bad
field access. Without it neither error named anything at all.

## Defect 1 — `Any`-escape checker reads `.kind` off a nil declared type (FIXED)

```
[field-access-error] field=kind recv_type=nil recv=nil expr=Identifier("t")
  stack=cli_native_build -> compiler_driver_run_compile -> compile ->
  lower_and_check_impl -> run_any_escape_pass -> any_escape_check ->
  any_check_function -> any_check_block -> any_check_expr -> any_check_block ->
  any_check_stmt -> any_type_is_any
error: semantic: undefined field 'kind': cannot access field on value of type 'nil'
```

`HirStmtKind.Let` is declared `Let(symbol: SymbolId, type_: HirType, init: HirExpr)`
(`hir_definitions.spl:749`) — `type_` is NOT optional. But HIR lowering builds
**desugared** bindings with no declared type at all, passing `nil`, at 10+
sites: tuple destructure (`statements.spl:200,233,287`), `for`-index temps
(`:327,533`), match scrutinee temps (`_Expressions/match_desugaring.spl:26,407,780`).
MIR ignores the field, so nothing else noticed. `any_check_stmt`'s `Let` arm
then calls `any_type_is_any(type_)` / `any_type_mentions_any(type_)`, both of
which `match t.kind` unconditionally, and the whole compile aborts.

**Fix:** `src/compiler/35.semantics/any_escape/checker.spl` — both predicates
return `false` for a nil type. An absent annotation is not a declared `Any`:
§8.1 is about what the source WROTE, and the value's own type is judged where
it is used. Not fixed at the 10+ lowering sites: `nil` is the established
convention for "no annotation" there, and synthesising a type would change HIR
semantics for every consumer.

**Reproduce spec:** `test/01_unit/compiler/semantics/any_escape/any_escape_spec.spl`,
case *"survives a desugared binding that carries no declared type"*, over the
new fixture `test/fixtures/any_escape/tuple_destructure_binding.spl`. Pre-fix
8 pass / 1 fail; post-fix 9/9.

## Defect 2 — `if val get_value = ...` binds to a FUNCTION, not the value (OPEN)

With defect 1 fixed the same build gets further and dies here instead:

```
[field-access-error] field=id recv_type=function recv=function = <fn:get_value>
  expr=Identifier("elem_local")
  stack=lower_module -> lower_function -> lower_function_with_gpu_metadata ->
  lower_block -> lower_block_expected -> lower_stmt -> lower_stmt_impl ->
  lower_expr -> lower_expr_impl -> lower_for -> lower_for_iterator ->
  lower_for_array_indexed
error: semantic: undefined field 'id': cannot access field on value of type 'function'
```

`src/compiler/50.mir/mir_lowering_stmts.spl:2711-2712` writes

```
if val get_value = get_call:
    elem_local = get_value
```

and `get_value` resolves to the module-level `fn get_value` declared in a
DIFFERENT module of the same compile closure
(`src/compiler/70.backend/backend/llvm_lib_translate_expr.spl:868`) instead of
to the `if val` binding. `elem_local` is therefore a function value and
`elem_local.id` fails.

This is the **same** error that fails the engine-differential native lane:
after the two harness problems below are removed, every fixture's
`native-build` ends in exactly this `undefined field 'id' ... type 'function'`.
So defect 2 alone keeps that lane at 0-for-13.

Not yet minimised: a same-file `if val get_value = o:` shadowing a same-named
`fn get_value` resolves CORRECTLY under `run`, and a two-module standalone
fixture also resolves correctly — the collision so far reproduces only inside
the compiler's own closure. **Do not "fix" this by renaming the local**: that
is the workaround this repo's rules forbid, and it would leave the resolver
defect live for every other same-named pair.

## Harness problems found alongside (engine-differential lane)

1. `scripts/check/check-engine-differential.shs:77` gates on `[ ! -d .git ]`.
   In a linked `git worktree` `.git` is a **file**, so the wrapper reports
   `ERROR — must run from the repo root` and refuses to run anywhere but the
   primary checkout. Fixed here to `[ ! -e .git ]`.
2. The native lane shells out to the relative path `bin/simple`. That path is
   gitignored, so in a fresh worktree it does not exist and every fixture
   reports `LANE_ERROR -- ... /bin/sh: 1: bin/simple: not found` — a lane-wide
   failure whose cause reads like a compiler defect. Left as-is (the lane is
   specified to run from a deployed checkout) but recorded so the next reader
   does not chase it.

## Defect 2, corrected diagnosis (2026-08-22) — NOT a name-resolution bug

The first write-up above (and the working hypothesis that followed it: "a local
binding must shadow an imported callable; the shared symbol registry consults
imported callables before local scopes") is **wrong**. Four independent
standalone reproductions of that shape all behave CORRECTLY on the deployed
seed:

| fixture shape | result |
|---|---|
| same file: `fn get_value` + `if val get_value = o:` … `return get_value` | correct |
| same file, binding assigned OUT of the `if val` into an outer `var` | correct |
| 3 modules, no import edge between the collider and the user, `pub fn get_value` | correct |
| 3 modules, collider NON-pub, reached only through a glob | correct |
| collider declared as an enum-BODY method `fn get_value(self)` | correct |

Instrumenting the real site settled it. With an `eprint` on either side of
`mir_lowering_stmts.spl:2711`:

```
[probe-forarr] get_call_present=LocalId(id: 27)
[probe-forarr] bound branch taken
[probe-forarr] get_call_present=LocalId(id: 66)
[probe-forarr] bound branch taken
```

The `if val` binds, takes the bound branch, and yields a real `LocalId` — the
resolution order is fine. The build then dies **somewhere else entirely**:

```
[field-access-error] field=id recv_type=function recv=function = <fn:get_value>
  expr=Identifier("local")
  stack=main -> cli_native_build -> ... -> aot_compile -> borrow_check ->
  check_mir_module -> check_function -> analyze_mir_borrows ->
  analyze_instruction -> record_operand_use
```

`record_operand_use` (`src/compiler/55.borrow/borrow_check/mod.spl:344-353`)
is `match op.kind: case Copy(local): nll.record_use(point, Place.local(local.id))`.
So `local` here is a **match payload binding**, not an `if val` binding, and it
too holds `<fn:get_value>`.

The load-bearing observation is that **two unrelated enums yield the same bogus
value**: `Option<LocalId>` in `lower_for_array_indexed` and `MirOperandKind` in
`record_operand_use` both produce the function `get_value` as their payload. A
name-resolution defect would be per-NAME (`elem_local` vs `local` are different
names); this is per-VALUE. What is broken is **enum payload extraction handing
back a stale/foreign value** — the same defect class as
`doc/08_tracking/bug/hir_enum_payload_blockvalue_unresolved_2026-08-21.md` and
the JIT optional-unwrap payload-read fix in `20416a1bda7`, not the symbol
registry, `registered_import_memo`, or `SymbolTable.define`.

Where `<fn:get_value>` itself comes from is still open. The only `get_value`
declarations in the compiler closure are an enum-body method on `CompileResult`
(`src/compiler/00.common/driver_compile_result.spl:16`) and a free
`fn get_value` in `70.backend/backend/llvm_lib_translate_expr.spl:868`; neither
is imported by either failing module, which is consistent with a slot/value
mix-up rather than a lookup.

**Next step for whoever picks this up:** do not touch the symbol registry.
Instrument enum payload extraction (interpreter path, the seed's
`rt_enum_payload` / match-arm binding) and print the discriminant and payload
provenance at `record_operand_use`; the two call sites above are reliable,
7-minute reproductions:

```
simple native-build test/fixtures/engine_differential/text_bytes_and_chars.spl -o /tmp/x --threads 2
simple native-build --source src/compiler --entry src/compiler/80.driver/driver_public_api.spl -o /tmp/y --threads 2
```

Both need `SIMPLE_DEBUG_FIELD_ACCESS=1`, without which neither names anything.

## Defect 2, round 3 (2026-08-22) — producer located, gated diagnostic landed

`SIMPLE_DEBUG_ENUM_PAYLOAD=1` (new, default off) reports any enum payload slot
that holds a `Value::Function`, at both the READ and the WRITE. Instrumented
sites, all in the seed:

| side | site tag | file |
|---|---|---|
| read | `match-arm` | `compiler/src/interpreter_patterns.rs` (enum payload destructure) |
| read | `if-val` | `compiler/src/interpreter_control.rs` (`optional_let_binding`) |
| write | `fn-return-some-wrap` | `compiler/src/interpreter_call/core/function_exec.rs` (implicit `T -> Option<T>` on return) |
| write | `variant-construction` | `compiler/src/interpreter_call/mod.rs` (6 sites), `compiler/src/interpreter_method/mod.rs` |

On the `text_bytes_and_chars` reproduction it fires 4 writes and 2 reads. The
**write** names the producer exactly:

```
[enum-payload-function] site=variant-construction enum=MirOperandKind variant=Copy
  slot=0 fn=get_value def_ptr=0x5bcafccd810
  stack=... lower_for -> lower_for_iterator -> lower_for_array_indexed ->
  decode_runtime_value -> mir_operand_copy
```

So the corrupt `MirOperandKind.Copy(<fn:get_value>)` is built by
`mir_operand_copy(raw)` inside `decode_runtime_value`
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:873`), whose `raw`
argument is `elem_local` from `lower_for_array_indexed`
(`mir_lowering_stmts.spl:2710-2714`). The read fires later in
`record_operand_use` and the compile dies there. **`elem_local` therefore IS
the function at the write** — the corruption happens at or inside

```
if val get_value = get_call:
    elem_local = get_value
```

which puts the ORIGINAL name-resolution hypothesis back in play in a narrower
form: the branch is entered correctly (an earlier `eprint` probe shows
`get_call_present=LocalId(id: 27)` / `bound branch taken`), so what is wrong is
the **body's read of `get_value`**, not the binding decision.

**But it still does not reproduce standalone.** Six shapes now, all correct on
this seed, including the closest one: an `impl`/`me` method doing
`if val get_value = o:` … `elem = get_value` while a DIFFERENT module in the
program declares `fn get_value(value_map: {i64: i64}, local_id: i64)` with the
same signature as the real collider, under both `run` and `native-build`.
Something the full compiler closure adds is still missing from the fixture.

**Ruled out this round:** the interpreter↔native value bridge is not the
producer. `value_bridge.rs:348` encodes an enum as the string
`"EnumName::Variant"` with `payload: 0`, and `:603` decodes it with
`payload: None` — that path **drops enum payloads entirely** rather than
corrupting them. (That is a real latent lossy conversion and should be filed
separately; it is not this bug.)

**Next step:** the remaining difference between the failing site and the green
fixtures is the closure, not the shape. Bisect by shrinking the real module
rather than by growing a fixture: the diagnostic now names the exact frame, so
a cut-down `mir_lowering_stmts.spl` that still fires
`site=variant-construction ... fn=get_value` is a much shorter path to the
minimal case than another synthetic guess.

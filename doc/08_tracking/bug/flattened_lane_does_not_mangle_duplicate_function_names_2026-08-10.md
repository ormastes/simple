# Module flattening does not mangle duplicate free-function names, so codegen cannot tell two `main`s apart

**Status:** FIXED in the flattened HIR/codegen (JIT) lane, 2026-08-10.
The six `cstart.spl` files are NOT yet buildable — see "What is still blocked".

## Resolution (2026-08-10)

The filed root cause was close but not exact, and the difference matters.
Flattening does not merely *fail to rename* a duplicate `main`: for an IMPORTED
module it **dropped the function outright**.
`pipeline::module_loader::strip_flattened_import_nodes` had

```rust
Node::Function(function) => {
    if function.name == "main" {
        continue;          // <- imported `main` discarded
    }
```

so there was never a second `main` to disambiguate. The alias had no definition
to bind to and resolved to the ENTRY module's `main`, which is why the probe
recursed. Mangling duplicates alone would therefore NOT have fixed this — there
was nothing to mangle.

The fix keeps the drop's original intent (an imported `main` must never become
or collide with the program entry symbol) while preserving the body:

1. `strip_flattened_import_nodes` **renames** the imported `main` to
   `flatten_owner_mangled_name(owner, "main")` instead of dropping it.
2. `interpreter_state::flatten_owner_mangled_name` is the new shared helper,
   ported from the native-project lane's long-standing scheme
   (`pipeline/native_project/imports.rs`, `raw_to_mangled`, which stores
   `sanitize_mangled(format!("{module_prefix}__{name}"))`). The native lane
   compiles module-by-module, so its `all_mangled`/`use_map` tables could not be
   reused wholesale; the *scheme* — owner path prefix + sanitize — is what
   ports.
3. `Lowerer::collect_flattened_import_aliases` recomputes the same symbol from
   the import marker's `source_owner` field (`normalize_path_key`, the identical
   string the flattener mangles with), so producer and consumer agree without a
   side table. The blanket `source_name == "main"` refusal is gone; a source
   that is still absent or ambiguous is left UNRESOLVED on purpose.

This is a **Rust seed** change, not `.spl`: the flattener, the import-binding
markers and HIR lowering are all in `src/compiler_rust/compiler/src/`. The
defect lives there, so the fix does too.

### Evidence

| lane | before | after |
|---|---|---|
| interpreter | `R:42` | `R:42` |
| codegen, alias left unresolved (shipped state) | hard error on `baremetal_main` | — |
| codegen, naive bare-name rewrite | `fatal runtime error: stack overflow`, rc=134 (reproduced independently) | — |
| codegen, this fix, `SIMPLE_JIT_STRICT=1` | — | **`R:42`** |

`R:42` is `argc + 41` from `target.spl`, a value reachable ONLY from the correct
function; the entry `main` returns nothing and recurses. Resolution is verified,
not compilation.

- `scripts/check/check-flattened-owner-mangling.shs` — **PASS, 4 cases**. Run
  against the pre-fix binary it is **FAIL 4/4** (proved live, not asserted).
- `scripts/check/check-import-alias-codegen.shs` — still **PASS 5/5**.
- `cargo test -p simple-compiler --release --lib --tests` — 44 failures before
  the change and the **same 44** after (`comm` diff empty in both directions).
  All 44 pre-exist on `origin/main` and are unrelated (GPU counters, VHDL, C
  linker detection, native_project stage4).

### What is still blocked

The six `src/os/kernel/arch/*/cstart.spl` files (`arm32`, `arm64`, `riscv32`,
`riscv64`, `x86_32`, `x86_64` — note `arm64`, not `aarch64` as first filed) are
**still not buildable**, for two reasons unrelated to mangling:

1. They abort earlier in HIR lowering on `Cannot infer field type: struct
   'MemoryRuntimeMapping' field 'address_space_root'` — identically before and
   after this fix. Running the files is consequently NOT a valid oracle for this
   defect; it cannot distinguish bound from unbound.
2. The AOT `simple compile` lane resolves no selective-import alias at all, not
   just `main`: a plain `use t.{helper as aliased_helper}` also fails with
   `Undefined("undefined identifier: aliased_helper")`. That is the parent bug
   (`aliased_use_import_does_not_bind_in_transitive_module_2026-08-10.md`) still
   open for the AOT path, and it is the one that actually gates baremetal.

Their shared import line IS verified: case 4 of the check compiles
`use os.runtime.baremetal.runtime_minimal.{main as baremetal_main, __spl_exit}`
— byte-identical to `cstart.spl:5` — against the real module and confirms
execution reaches `runtime_minimal.main`, whose body is `__simple_main() as i32`
(positive identification via the `__simple_main not found` report, not inferred
from an absent error). Pre-fix that case reports unresolved `baremetal_main`.

**No board or QEMU real-firmware evidence exists for this change**, and none is
claimed: the six units still do not compile, so nothing was booted. Per
`.claude/rules/board-runnable.md` this is scoped explicitly — the fix is
verified at the symbol-resolution level in the JIT codegen lane only.

---

**Original report (root cause partly superseded — see above).**

**Status:** OPEN — root-caused 2026-08-10 with a measured reproducer.
**Filed:** 2026-08-10
**Parent:** `doc/08_tracking/bug/aliased_use_import_does_not_bind_in_transitive_module_2026-08-10.md`
(this is the sub-case that fix deliberately left RED).

## Defect

`pipeline/module_loader.rs` merges every imported module's items into one
flattened `Module`. It **never renames**: two modules that both define a free
function `main` are both pushed as `Node::Function { name: "main" }`
(`module_loader.rs:672`, and the bulk `items.extend(...)` at 2195/2253/2303/2360).

The only disambiguator carried is the synthetic attribute
`__simple_flatten_module_owner__=<path>` attached by `tag_function_module_owner`
(`interpreter_state.rs:63,102-112`). Every reader of that attribute is in the
interpreter (`interpreter_eval.rs:519`, `interpreter_call/core/function_exec.rs`,
`interpreter_module/...`, `module_cache.rs`, `module_loader.rs:1441`).
**Nothing under `hir/` or `codegen/` consumes it.**

HIR lowering is consequently last-wins on the bare name
(`hir/lower/module_lowering/module_pass.rs:390-393`):

```rust
Node::Function(f) => {
    let ret_ty = self.resolve_type_opt(&f.return_type)?;
    self.globals.insert(f.name.clone(), ret_ty);
```

while BOTH bodies are still pushed unmangled into `self.module.functions`
(`module_pass.rs:1428-1431`, `:1850-1853`). Two HIR functions named `main`, no
error, no mangling.

## Measured reproducer

```
target.spl:  pub fn main(argc: i32, argv: i64) -> i32:  return argc + 41
mid.spl:     use target.{main as baremetal_main}
             pub fn cstart_init(n: i32) -> i32: return baremetal_main(n, 0)
entry.spl:   use mid.{cstart_init}
             fn main(): print("R:" + cstart_init(1).to_text())
```

| lane | result |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | `R:42` — correct |
| codegen, resolving the alias to the bare name `main` | `thread 'simple-main' has overflowed its stack / fatal runtime error: stack overflow` |

The alias bound the ENTRY module's `main`, so `cstart_init` recursed into the
program entry point. Silently wrong code.

## Why it is currently masked, not fixed

The parent fix refuses to rewrite an alias when the source name is `main`, or
when the source name has more than one definition in the flattened unit. Those
aliases stay unresolved and keep the honest hard error:

```
error: Cranelift JIT compile: SIMPLE_JIT_STRICT: unresolved external symbol
       'baremetal_main' would NULL-jump in JIT; refusing to fall back
```

That is a deliberate choice — an error beats miscompilation — but it means the
six highest-priority victims are still dead in the codegen lane:

- `src/os/kernel/arch/{x86_64,aarch64,riscv64,...}/cstart.spl:5`
  `use os.runtime.baremetal.runtime_minimal.{main as baremetal_main, __spl_exit}`

These units are compiled AOT for baremetal targets, where **no interpreter
fallback exists**, so this is the hard-`E1002` regime.

## Fix shape

Give the flattened lane owner-unique symbol names, one of:

1. Mangle duplicated free-function names at flatten time with their owner path
   (the native-project lane already has exactly this: `all_mangled` /
   `qualified_import_functions`, `pipeline/native_project/imports.rs:942-1102`,
   whose values are mangled unique symbols, not bare names). Reuse it for the
   flattened lane instead of maintaining two schemes.
2. Or teach HIR lowering to consume `__simple_flatten_module_owner__=` and key
   `globals` / `module.functions` on `(owner, name)`.

(1) is preferred: the mechanism exists and is already proven in the native lane.

Note this defect is **not** alias-specific. Any flattened unit with two
same-named free functions is last-wins in codegen today; the alias case is
merely how it was caught.

## Unblock condition

The reproducer above prints `R:42` under `SIMPLE_JIT_STRICT=1`, the
`source_name == "main"` and duplicate-count guards in
`Lowerer::collect_flattened_import_aliases` are removed, and
`sh scripts/check/check-import-alias-codegen.shs` still PASSes 5/5.

## Do not

Do not close this by renaming `main` in `runtime_minimal.spl` or by rewriting
the six `cstart.spl` imports to plain imports. Both hide the defect; the alias
form is valid grammar and duplicate names across modules are legal.

## Follow-up, same day: selective-import aliases never resolved in the AOT lane

Found while re-measuring the fix above. Both defects below are independent of
the `main` collision and of each other; both were RESOLVED in the follow-up
commit, verified by running the linked binary, not by compiling it.

Reproduced isolated from the `cstart.spl` HIR error, on a two/three-file
synthetic with a plain non-`main` alias (`use target.{base_get as g}`):

| placement of the alias | lane | pre-fix result |
|---|---|---|
| ENTRY module | `compile --native` | `error: codegen: undefined symbol: g` |
| ENTRY module | JIT (`SIMPLE_JIT_STRICT=1`) | `unresolved external symbol 'g'` |
| IMPORTED module | `compile --native` | `error: semantic: Undefined("undefined identifier: g")` |
| IMPORTED module | JIT | already green (this is the shape `check-import-alias-codegen.shs` probes) |

**Defect 1 — entry-module alias, BOTH lanes.** The entry module's own `use`
survives flattening (an imported module's does not), and lowering registers a
phantom callable *and* global under the ALIAS name from it. In
`hir/lower/expr/mod.rs::lower_identifier` the alias-map consultation was
deliberately the LAST attempt, so those two phantom branches won and emitted
`Global("g")` — a symbol nothing defines. The alias map was correctly populated
the whole time (probe-confirmed), so this was never a collection failure. Fixed
by ordering the alias branch after locals but BEFORE the callable/global
lookups; shadowing of a REAL declaration is prevented at the source instead —
`collect_flattened_import_aliases` now refuses to record an alias whose local
name is declared anywhere in the flattened unit (function, const, static or
module-level let), where it previously checked functions only.

**Defect 2 — imported-module alias, AOT only.** An imported module's `use` is
replaced at flatten time by a marker const, and the TYPE CHECKER bound nothing
for it, so `g` was `undefined identifier` and the AOT lane aborted the unit
before HIR lowering ever ran. The JIT lane does not gate on that check, which is
exactly why the existing check — whose alias lives in a mid module — stayed
green while the AOT lane resolved zero aliases. Fixed in
`type/src/checker_check.rs`: the module pre-pass now binds the marker's local
name to a fresh var, the same binding `register_import_aliases` already makes
for the entry-module form.

Both fixes are Rust-seed edits because both defects live in seed-side lowering
and type checking, the same components as the two fixes preceding them.

Checks: `scripts/check/check-import-alias-aot.shs` — PASS 4/4 after; against the
pre-fix binary `--expect-fail` reports `negative control live` with both alias
forms broken and both plain controls still resolving (run live, not asserted).
`check-import-alias-codegen.shs` PASS 5/5 and `check-flattened-owner-mangling.shs`
PASS 4/4 unchanged. `cargo test -p simple-compiler --lib`: failure SET identical
before and after, no new failures.

**`cstart.spl` is still blocked** and this fix does not unblock it. After the
fix, `simple compile src/os/kernel/arch/x86_64/cstart.spl --native` fails on
`semantic: Undefined("undefined identifier: Result")`, downstream of the
separately-tracked `MemoryRuntimeMapping.address_space_root` HIR error. No
board-runnable claim follows from this change.

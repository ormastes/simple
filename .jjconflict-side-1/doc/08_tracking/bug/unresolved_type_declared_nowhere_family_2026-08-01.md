# "Unresolved type" family: lower_named_kind whitelist drift, not source defects

**Date:** 2026-08-01
**Status:** Class A **closed except the cross-module struct fallback**.
Scalars (`usize`/`isize`/`u128`/`i128`/`unit`) landed in `085dfec41`;
`Self`, `tuple`, `Map`/`HashMap`/`dict`/`set`, the single-uppercase-letter rule
and `has_X` landed in the follow-up commit that added this paragraph.
Class B **CLOSED** 2026-08-01 — the owner chose the alias: `Int`/`Bool`/`Char`
landed with call sites unchanged; `Float`/`Vec` verified wrong and deliberately
not aliased. One new defect split out: generic applications reach the gate with
the name `Any` (`Vec<i64>` and `list<i64>` both fail as `unresolved type: Any`).
**Component:** `src/compiler/20.hir/hir_lowering/types.spl` — `HirLowering.lower_named_kind`
(plus `20.hir/hir_lowering/_Items/module_lowering.spl` for the `Self` scope fix)

## Summary

A stage4 A/B run reported 1,484 `unresolved type` errors and framed the two
largest buckets — `Int` (x187) and `usize` (x66) — as **source defects**: "types
that are used but declared nowhere in the tree", unfixable by any resolver
change.

That framing is **wrong for `usize` and right for `Int`**. The distinction
matters because acting on the original framing would have meant rewriting ~1,300
`usize` annotations to `i64`, discarding signedness and normalizing a workaround
around a compiler bug.

## The actual mechanism

`lower_named_kind` is the **single strict gate** that emits
`unresolved type: {name}`. It matches a hardcoded whitelist of type names and
falls through to `self.symbols.lookup_or_invalid(name)`; a miss is a hard error
that collapses the declaration to `HirTypeKind.Error`.

That whitelist has **drifted from the Rust seed's resolver**
(`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs`). The seed accepts a
strictly larger set of bare scalar/container names.

Critically, **no seed-driven probe can detect the drift**. The seed resolves any
unknown type name to `ANY` under `lenient_types`, so both `simple_seed run` and
`simple_seed compile ... -o out.smf` accept a deliberately bogus type, exit 0,
and emit an artifact. Verified directly: a probe annotated
`ZzzNotARealTypeQqq` compiled to a present `.smf` with `rc=0`. Only driving
`HirLowering` in-process and asserting `errors.len()` gates this.

## Census (owned `.spl`, excluding `src/compiler_rust/vendor/**`, `src/runtime/vendor/**`)

Type-position uses (`: N`, `-> N`, `[N]`, `<N,..>`), string literals and
comments stripped:

| name      | all uses | all files | src uses | src files | in seed? | in pure-Simple (before fix)? |
|-----------|---------:|----------:|---------:|----------:|----------|------------------------------|
| `usize`   |     1303 |       146 |     1194 |       131 | yes      | **no** -> FIXED              |
| `Int`     |     1093 |       167 |      599 |       108 | **no**   | **no** -> open (Class B)     |
| `Self`    |      517 |        48 |      485 |        34 | yes      | **no** -> FIXED              |
| `Bool`    |      352 |       103 |      297 |        76 | **no**   | **no** -> open (Class B)     |
| `tuple`   |      313 |        65 |      220 |        58 | yes      | **no** -> FIXED              |
| `dict`    |      101 |        21 |       36 |        10 | yes      | **no** -> FIXED              |
| `Map`     |       56 |        21 |       40 |        13 | yes      | **no** -> FIXED              |
| `HashMap` |       37 |        12 |       27 |         8 | yes      | **no** -> FIXED              |
| `Vec`     |       37 |        11 |       35 |         9 | **no**   | **no** -> open (Class B)     |
| `u128`    |       36 |         7 |       18 |         2 | yes      | **no** -> FIXED              |
| `set`     |       23 |        14 |       11 |        10 | yes      | **no** -> FIXED              |
| `unit`    |       16 |        15 |        7 |         6 | yes      | **no** -> FIXED              |
| `Float`   |       12 |         9 |        5 |         4 | **no**   | **no** -> open               |
| `Char`    |        9 |         5 |        9 |         5 | **no**   | **no** -> open               |
| `i128`    |        1 |         1 |        0 |         0 | yes      | **no** -> FIXED              |
| `isize`   |        0 |         0 |        0 |         0 | yes      | **no** -> FIXED (parity)     |

The stage4 per-name counts (187, 66) are far below these totals because that run
**aborts inside phase 3** on a separate arena desync (6,474 `[stmt_get_tag] OOB`
/ `arena_len=0` events, first on log line 1). Its counts are early-abort
artifacts and were **not** used as evidence here. Stage3 is also useless for
this: it runs the bootstrap-flat pipeline and never performs this lowering.

## Class A — compiler parity gap (NOT source defects)

`usize`, `isize`, `u128`, `i128`, `unit`, `tuple`, `Self`, `Map`, `HashMap`,
`dict`, `set`. The seed accepts all of these. For `usize` specifically, three
further layers of *this* compiler already handle it:

- `HirType.named` (`20.hir/hir_types.spl`) -> `Int(bits:64, signed:false)`;
  `isize` -> `Int(bits:64, signed:true)`
- `30.types/_TypeLayout/{layout_core,arch_and_verify}.spl` -> 8 bytes
- `70.backend/target/riscv32.spl` -> 4 bytes; `80.driver/shb/shb_types.spl`
  registers a `usize` layout entry

Only `lower_named_kind` lacked the arm. **Fixed in `085dfec41`** for the scalar
subset (`usize`/`isize`/`u128`/`i128`/`unit`).

### Follow-up: remaining Class A gaps closed

Every remaining Class A name now resolves. Each arm below states the type it
maps to and whether that matches the seed:

| spelling | maps to | seed parity |
|----------|---------|-------------|
| `Self` | the enclosing class / impl type, `HirTypeKind.Named(owner, [])` | **exact** — seed `resolve_self_type()` returns `current_class_type` |
| `tuple` | `HirTypeKind.Tuple([])` (empty element list) | **exact** — seed registers `HirType::Tuple(vec![])` |
| `Map` / `HashMap` with 2 args | `HirTypeKind.Dict(k, v)` | **exact** — seed `type_resolver.rs:459` |
| `Map` / `HashMap` argless | `HirTypeKind.Any` | **exact** — seed `:182` / `:464` |
| `dict` / `set` | `HirTypeKind.Any` | **exact** — seed `:182` |
| single uppercase letter (`T`/`K`/`V`) | `HirTypeKind.Any` | **exact** — seed `:141` |
| `has_X` | `HirTypeKind.Optional(lower(X))` | **exact** — seed `:128` |

No arm changes signedness or width, so the divergence recorded below stays
confined to `usize`/`isize`.

**Ordering is load-bearing, not incidental.** In the seed, `tuple`, the bare
container names and the single-letter rule all sit **after**
`self.module.types.lookup(name)`; only `has_X` (and the `?` suffix) run before
it. That order is reproduced exactly, because this tree really does declare
types named `Map` (1 struct), `HashMap` (2 classes + 1 struct) and `Set`
(2 structs) — hoisting those names into the match above the symbol lookup would
shadow real user types and silently retype their annotations to `Any`. A
regression spec (`lets a really declared Map struct win over the bare-container
rule`) pins this. `has_X` is safe to run before the lookup only because **no**
type in the tree is declared `has_*` (verified by declaration grep).

### `Self` was not a table entry — root cause

`Self` needed a second fix, in a different file. `lower_named_kind` already had
the context it needed (`current_method_self_type`, the exact analogue of the
seed's `current_class_type`), but the annotation was being resolved **before**
any class/impl scope was entered.

The mechanism, **PROVED** by dumping the parsed module rather than inferred: the
parser desugars a method-carrying `class C:` into a class whose method dict is
**empty**, plus a synthetic `impl` block (`classes["Widget"].methods` empty while
`module.impls.len() == 1`). Class methods therefore flow through the impl-method
branch of the up-front signature-declaration pass in
`module_lowering.spl`, which runs at **module scope** where
`current_method_self_type` is still nil. The class-body scope
(`declaration_lowering.spl:528`) and the impl scope
(`trait_impl_lowering.spl:199`) are both established later and so could never
help a `-> Self` in a *signature*.

Fix: publish the self-type around that signature loop, reusing the owner symbol
the loop already computed for `method_symbol_name`, saved/restored exactly like
the two existing scopes. A single instrumented run confirmed `Self` was reached
exactly once and with a nil context, which is what localised this.

**Still open — the cross-module struct fallback.** The seed falls back to
`global_struct_defs` for a struct used by name without an explicit `use`
(`type_resolver.rs:151`). This is the one rule that is **not** portable as a
table entry: pure-Simple HIR lowering has **no `global_struct_defs` equivalent
at all** (grep for `global_struct`/`global_defs` over `src/compiler/**` returns
nothing). Porting it means building and threading a cross-module struct
registry, which is a design change rather than a parity patch, so it is left
open deliberately rather than approximated.

Correction to the previous revision of this doc: there is **no seed `X_opt`
normalization**. The seed has exactly two name rewrites, a `?` *suffix*
(`:119`) and a `has_` *prefix* (`:128`); `resolve_type_opt` (`:502`) is an
unrelated helper that resolves an absent `Option<Type>` AST annotation to
`VOID`. The earlier `X_opt` claim was a misreading of that function name.

## Class B — genuine source defects (capitalized-primitive dialect)

`Int` (1093), `Bool` (352), `Float` (12), `Char` (9). Accepted by **neither**
resolver.

These are **not** N independent bugs — they are **one dialect**, and it is
already half-blessed: `lower_named_kind` has
`case "text" | "str" | "String": HirTypeKind.Str`, so the capitalized `String`
spelling from the same dialect **already resolves**. The affected files use the
spellings together in single signatures, e.g.
`fn name_lint_parse_class(trimmed: String, indent: Int, line_num: Int)`
(`src/compiler/90.tools/lint/_LintMain/name_lints.spl:71`). Fixing `Int` but not
`String` in either direction leaves the tree incoherent.

Two further amplifiers, both confirmed:

1. **Tier mirroring.** `src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/`
   each hold a copy of the `lsp/` and `dap/` trees, and `src/app/dap/` mirrors
   them again — so `protocol.spl` alone contributes 17 uses x 4 copies. A fix
   must be applied across mirrors or it will regress.
2. **Test-tree mirroring.** `test/03_system/feature/...` and
   `test/feature/...` are duplicate paths with identical counts (27/27, 21/21,
   19/19, 17/17).

**Decision required before acting** (deliberately not taken unilaterally):

- **Option A — alias in the compiler.** Add `Int`/`Bool`/`Float`/`Char` arms
  next to the existing `String` arm. Two lines, no source churn, internally
  consistent with `String`. Risk: blesses a dialect that
  `35.semantics/lint/primitive_types.spl` explicitly calls the "canonical
  bare-primitive type table -- SINGLE SOURCE OF TRUTH" and lists as
  lowercase-only, with parity enforced by
  `test/01_unit/compiler/lint/primitive_types_parity_spec.spl`.
- **Option B — rewrite use sites.** `Int`->`i64`, `Bool`->`bool`, and for
  coherence `String`->`text`. Matches the canonical table, but touches ~1,450
  sites across ~170 mirrored files, and `String` currently compiles — so this is
  a behaviour-preserving churn on the `String` half and a fix only on the rest.

`Vec` (37 uses) is a third case: a Rust spelling with no counterpart in either
resolver and no `String`-style precedent. Likely a genuine port artifact; should
become `[T]`.

### RESOLVED 2026-08-01 — Option A (alias), user-chosen. Class B CLOSED.

The owner decision landed: **Option A**, alias in the compiler, **all call sites
left unchanged**, the rewrite deliberately not taken. Implemented in
`lower_named_kind`, in the same post-symbol-lookup `elif` chain as the Class A
container rules.

**Only three of the five candidate names were aliased.** Each mapping was
verified against real use sites first; two turned out to be wrong and are
recorded here rather than landed as plausible guesses.

| spelling | maps to | owned type-position uses | seed parity |
|---|---|---:|---|
| `Int` | `HirTypeKind.Int(64, **signed**)` | 524 under `src/` | **none** — seed has no arm; `ANY` under `lenient_types`, `UnknownType` strict |
| `Bool` | `HirTypeKind.Bool` | 208 under `src/` | **none** — same |
| `Char` | `HirTypeKind.Char` | 3 (`is_identifier_char(c: Char) -> Bool`, x3 lsp tiers) | **none** — same |
| `Float` | **NOT aliased** | **0** | **none** — same |
| `Vec` | **NOT aliased** | **0** bare | **none** — same |

**This family is the only one in this file that is NOT seed parity.** The seed's
`type_resolver.rs` has no arm for any of the five, so the alias makes this
compiler *stricter and more precise* than the seed here (a real `i64`/`bool`/
`char` instead of `ANY`), never looser.

**No width/signedness divergence is introduced.** `Int` takes the **signed**
64-bit kind, matching the tree's own `type I64 = i64` and the `i64` any rewrite
would have produced; `Bool` and `Char` have no width axis. So the divergence
recorded under *Known divergence left open* stays confined to `usize`/`isize`.

**Placement is load-bearing** — the same rule the `Map`/`HashMap`/`Set` arms
already document. The arms sit **after** the symbol lookup, so a declared type of
the same name still wins. One really exists: `struct Bool: value: bool` in
`src/lib/*/ndarray/mod.spl` (all three tiers), used in type position by
`flat_bool(..) -> Bool` and `get_bool_at(..) -> Bool`. A top-level `case "Bool"`
would silently retype those returns from the boxed struct to a primitive `bool`.
Verified in-process: a module declaring `struct Bool` lowers with `errors=0` and
a `Named(..)` return kind, before and after. Pinned by the regression example
*does NOT shadow a user-declared type of the same name*.

**Why `Float` was rejected.** `Float` has **zero** genuine type-position uses in
owned `.spl`. The "12" in the census table above counted comment prose
(`# — Float-only arithmetic —`) and Rust source *inside string literals* in the
`src/app/ffi_gen.specs/runtime_value_full.spl` code generator. `Float` is also
**declared** — a marker `trait Float:` in `src/lib/*/simd/vector.spl` (three
tiers). An `f64` alias would be dead code whose only effect is shadowing risk.

**Why `Vec` was rejected.** Bare `Vec` has **zero** type-position uses in owned
`.spl`. Every real use is `Vec<T>` — and `Vec<T>` **never reaches
`lower_named_kind` under the name `Vec`**: the generic-argument path collapses
the name first, so `fn f(a: Vec<i64>)` fails as `unresolved type: Any`, not
`unresolved type: Vec`. A `case "Vec"` arm would not fix a single real site.
`Vec` is additionally SIMD-shaped in `src/lib/*/simd` (`Vec<f32,4>`,
`Vec<T, const N: usize>`), where `list` would be the wrong meaning even if the
arm could fire. The census row `Vec` (37) should be read as *`Vec<T>`
occurrences*, which this gate never sees.

**New defect split out (pre-existing, NOT fixed here): generic applications
reach the gate with the name `Any`.** `Vec<i64>`, `Vec<Foo>` **and `list<i64>`**
all fail identically with `unresolved type: Any`, even though bare `list`
resolves. The constructor name is lost before the strict gate sees it. Needs its
own lane — it is the reason no `Vec` arm can work, and it likely suppresses other
generic annotations too.

`src/type/simple_lang/` corroborates the three-name result: it blesses the same
dialect as real declarations (`type Bool = bool`, `type I64 = i64`,
`type Text = text`, plus F32/F64/U8..U64) — spelling the integer `I64`, and
carrying **no** `Float`, `Char` or `Vec` member.

The `primitive_types.spl` "single source of truth" risk flagged under Option A
did **not** materialise: `test/01_unit/compiler/lint/primitive_types_parity_spec.spl`
is still **4 examples, 0 failures** after the change. That table governs the
lint's lowercase bare-primitive set; the alias lives in HIR lowering's
declared-nowhere fallback and does not touch it.

## Evidence standard used

All findings are **static and local**. The parity gap is provable by reading the
two whitelists; the census is a grep over owned `.spl` with string/comment
stripping, using `/usr/bin/grep` (the default `grep` here is ugrep). The fix
carries an in-process A/B:

- with fix: **5 passed, 0 failed**
- without fix: **1 passed, 4 failed** (only the rejection control stays green)
- no parse regression: baseline and edited both reach the same semantic stage
  with an identical `56 function(s) contain` message

`test/01_unit/compiler/hir/seed_parity_scalar_type_names_spec.spl` carries a live
control asserting an undeclared name is still rejected, matched by **error
identity** rather than a count (the same annotation is reported once per
lowering pass, so a fixed count is brittle — the first draft of that control
asserted `1` and saw `2`).

### Follow-up evidence (`Self`/`tuple`/containers/single-letter/`has_X`)

`test/01_unit/compiler/hir/seed_parity_container_and_self_types_spec.spl`,
in-process A/B, **both directions**:

- with fix: **8 passed, 0 failed**
- without fix (both implementation files reverted to the base commit, spec
  unchanged): **3 passed, 5 failed** — and the 3 that stay green are exactly
  the three controls (undeclared name still rejected, `TK` still rejected,
  declared `Map` struct still wins). Every parity example goes red; no control
  moves in either direction.
- the pre-existing scalar spec still reports **5 passed, 0 failed** with the
  follow-up applied, so `085dfec41` is not regressed.

Three controls, not one, because two distinct weakenings had to be excluded:
accepting any unknown name (the `lenient_types` failure mode), and implementing
the single-letter rule without its `len() == 1` guard — which would have erased
whole undeclared type names like `TK` to `Any` while still passing the original
control.

**Harness non-vacuity was proved by sabotage before any of the above was
believed.** Renaming the landed `case "usize"` arm to a dead label turned the
scalar spec red (`3 passed, 2 failed`, exit 1), confirming the runner really
recompiles the edited pure-Simple source rather than serving a cached or seed
-resolved result.

**Two measurement traps hit and documented, so the next lane does not repeat
them:**

1. *Seed-as-host is fine; seed-as-oracle is the trap.* These specs are executed
   by the Rust seed binary, but the resolver under test is the pure-Simple
   `lower_named_kind` driven in-process — the seed only interprets the spec. That
   is not the false-green described above, and the sabotage run proves it.
2. *Directory-mode runs are void here.* `simple test test/01_unit/compiler/hir/`
   reports `44 total, 0 passed, 44 failed` with **no per-example `✗` lines** —
   and reports **exactly the same at the base commit**, unchanged by any edit.
   It is a pre-existing harness artifact of running many specs in one process
   (`parse_module_silent_checked` does not reset state between files), not a
   regression signal. Per-file verdicts require **one process per file**; the
   directory number must never be quoted as a result.

## Class C — generic applications erased to `Any` in the PARSER (root-caused 2026-08-01)

`fn f(a: Vec<i64>)` fails as `unresolved type: Any`. So do `Vec<Foo>`,
`list<i64>`, `list<list<i64>>`, `Map<text,i64>` and the SIMD `Vec<f32,4>`, while
bare `list` resolves to `Array<ANY>` and bare `Vec` correctly reports
`unresolved type: Vec`. This is NOT a `lower_named_kind` whitelist gap: the base
name is destroyed before the gate is reached, so no arm added to that match — a
`Vec -> list` alias included — can ever fire for a generic application.

### Root cause (PROVED)

`src/compiler/10.frontend/core/parser.spl` `parser_parse_type_impl`, the
"unknown generic type" tail of the `has_generic` branch:

- `Option` / `Result` / `Dict` are special-cased above it and keep their
  arguments through the dedicated `result_type_register` / `dict_type_register`
  side tables. That is why `Result<i64,text>` and `Dict<text,i64>` lower
  correctly today.
- Any other base is looked up with `named_type_find(type_name)`. On a hit it
  returns `TYPE_NAMED_BASE + gid` — the **name survives, the arguments are
  dropped**.
- On a miss it returns **`TYPE_ANY`**, which
  `_FlatAstBridge/convert_nodes.spl` decodes as `Named("Any", [])`. The
  annotation now literally spells `Any`, and `lower_named_kind` reports
  `unresolved type: Any` — naming a type nobody wrote.

The erasure is therefore conditional on the base being absent from **this
file's** named-type registry. `list`, `Vec` and `Map` are builtins or live in
other modules, so they always miss. This makes Class C a symptom of the same
missing cross-module type fallback recorded below, not an independent defect.

### Evidence

In-process `HirLowering` A/B (the only harness that can see this — see the
measurement traps below), 13 shapes:

| annotation | param0 lowers to | errors |
|---|---|---|
| `list` (bare) | `Array<ANY>` | 0 |
| `Dict<text,i64>` | `Dict<Str,Int>` | 0 |
| `Result<i64,text>` | `Result<Int,Str>` | 0 |
| `i64?` | `Opt<Int>` | 0 |
| `list<i64>` | `ERROR` | `unresolved type: Any` |
| `list<list<i64>>` | `ERROR` | `unresolved type: Any` |
| `Vec<i64>`, `Vec<Foo>` | `ERROR` | `unresolved type: Any` |
| `Map<text,i64>` | `ERROR` | `unresolved type: Any` |
| `Vec<f32,4>` (SIMD) | `ERROR` | `unresolved type: Any` |
| `Vec` (bare) | `ERROR` | `unresolved type: Vec` |
| `Foo<i64>`, `struct Foo<T>` declared | `Named(nargs=0)` | monomorphization #158 Phase B |

Discriminating confirmation that the running parser really implements the
branch above: a base declared **in the same file** keeps its name and lowers
clean (`struct Bar` + `fn f(a: Bar<i64>)` → 0 errors; `struct Map` +
`fn f(a: Map<text,i64>)` → 0 errors), while the identical shape with an
undeclared base (`Baz<i64>`) reports `unresolved type: Any`. Declared-vs-
undeclared is the only variable, which is exactly what `named_type_find`
gates.

### Why no fix is landed here

The one-line fix — register the base name instead of returning `TYPE_ANY`, as
the non-generic path immediately below already does — is **not safe to land
unverified**, for two independent reasons:

1. **It converts a lenient recovery into a hard error.** The `TYPE_ANY`
   fallback exists precisely because a generic base is usually declared in
   another module. Preserving the name sends it to the strict gate, where the
   missing cross-module fallback (see below) means it will NOT be found — so
   every cross-module generic annotation in the tree would turn from a silent
   `Any` into `unresolved type: <Name>`. Fixing Class C properly therefore
   **depends on** the cross-module struct fallback, which is still open.
2. **It cannot be measured from source.** See below.

A safe subset exists and is the recommended next step: preserve the base name
only for bases `lower_named_kind` can resolve **without** the symbol table
(`list`, `Map`, `HashMap`, `set`, `dict`, `tuple`), keeping `TYPE_ANY` for
everything else. That fixes `list<i64>`, `list<list<i64>>` and `Map<K,V>` with
no new hard-error surface, and leaves `Vec<i64>` as `Any` — correctly, since
`Vec` has no arm and is SIMD-shaped in `src/lib/*/simd`, where `list` would be
the wrong meaning.

Generic **arguments** remain dropped either way: `TYPE_NAMED_BASE + gid` is a
bare integer tag with nowhere to carry them, and the bridge decodes it as
`Named(type_tag_name(tag), [])`. Only `Dict` and `Result` keep arguments, via
their dedicated side tables. Carrying arguments for an arbitrary base needs a
general side table — a design change, not a patch.

### Measurement traps found while root-causing this (both false-greened)

1. **The JIT false-greens the whole family.** Running the in-process probe as a
   bare positional `.spl` (the Cranelift JIT) reported **`errors=0` for every
   shape, including the broken ones**. `hir.functions[fn_id]` returns nil under
   the JIT — the known Dict-with-struct-values defect — so the probe silently
   inspected nothing. The same probe under `SIMPLE_EXECUTION_MODE=interpreter`
   shows the real failures. Any in-process HIR probe here MUST pin the
   interpreter. (`simple test` already hard-defaults to it.)
2. **The pure-Simple core parser is NOT executed when driving the frontend
   in-process.** An `eprint` at the top of `parser_parse_type_impl` produced
   **zero** hits across a full probe run, and sabotaging both the unknown-
   generic return and the bare-name registration changed nothing, while
   sabotaging `lower_named_kind`'s message in `20.hir/hir_lowering/types.spl`
   showed up immediately. `compiler.core.parser` resolves to an implementation
   baked into the binary; only the HIR layer is read from `.spl` at runtime.
   **Consequence: a parser-layer fix in this family cannot be gated by any
   in-process probe — it requires a bootstrap rebuild to become observable.**
   This is why Class A/B fixes (all in `lower_named_kind`) were verifiable and
   Class C is not.

## Known divergence left open

`usize`/`isize` signedness follows `HirType.named` (unsigned/signed 64), **not**
the seed, which returns a signed `I64` for both. Observable only for `>>` on a
high-bit-set value: unsigned emits `ushr`, signed emits `sshr`. Recorded here
rather than silently normalized. The seed's own comment on `u128`/`i128` states
that picking `U64` there "would make the JIT emit ushr and silently diverge from
the interpreter on high-bit-set limbs" — the same reasoning may argue for signed
`usize`, but changing it would contradict this compiler's `HirType.named` and the
`u64` arm beside it. Needs a deliberate cross-engine decision.

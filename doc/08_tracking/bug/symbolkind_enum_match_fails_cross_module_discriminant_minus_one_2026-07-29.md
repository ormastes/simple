# Bug: `SymbolKind` enum-variant patterns never match through `HirLowering.symbols` — `rt_enum_discriminant` returns -1

- **Date:** 2026-07-29
- **Severity:** medium (silent — any `case SymbolKind.X:` gate on a `Symbol` pulled out of `HirLowering.symbols.symbols` silently never fires)
- **Area:** `SymbolTable`/`HirLowering` internals (`20.hir/hir_types.spl`, `20.hir/hir_lowering/*`), running under the seed's own execution of the self-hosted compiler's `.spl` source
- **Found by:** lane IMP2 (qualified-import-call fix), via isolated probes + in-place instrumentation (reverted). Re-investigated and narrowed by lane DISC1 (2026-07-30) with a live, deterministic repro plus a set of negative-control probes.

## DISC1 update (2026-07-30): "cross-module" was NOT the actual trigger — retitle candidate below

IMP2's title/diagnosis attributed this to crossing modules via two spellings
of the `src/compiler/hir -> src/compiler/20.hir` symlink. **That framing is
not supported by direct testing.** A live repro (below) shows the same
`kind_matched=false` / `rt_enum_discriminant == -1` result for a symbol
(`main`) whose `defining_module` is the *same* module as the match site —
no cross-module boundary is crossed for that symbol at all. So the true
trigger is broader than "cross-module": it is specific to `Symbol` values
retrieved out of `HirLowering.symbols.symbols` (a `Dict<i64, Symbol>`,
`SymbolTable.symbols` in `hir_types.spl:193`) via the real compiler's own
`self.symbols.define(...)` + bracket-index read path
(`get_symbol_raw`/`field_module_callable`'s `self.symbols.symbols[key]`
pattern, `hir_types.spl:360` / `expressions.spl:160`) — it happens for
*every* symbol reached that way, cross-module or not.

### Minimal live repro (reproduces on the currently-deployed binary, `bin/simple test`)

```simple
use compiler.hir.hir_lowering.types.{HirLowering, hirlowering_for_module}
use compiler.hir.hir_lowering.items.*
use compiler.hir.hir_lowering.module_surface.{ModuleSurfacesByName, module_surfaces_from_modules}
use compiler.hir.hir_definitions.*
use compiler.hir.hir_types.*
use compiler.frontend.frontend.{parse_full_frontend}
use compiler.frontend.parser_types.{Module}
use compiler.common.driver_core_types.{SourceFile}
use compiler.common.config.{Logger}

extern fn rt_enum_discriminant(value: Any) -> i64

describe "real SymbolKind.Module value, matched against SymbolKind.Module":
    it "an `import provider` module-alias symbol's .kind case-matches SymbolKind.Module":
        val log = Logger(level: 0)
        val src_provider = "pub fn answer() -> i64:\n    42"
        val provider = parse_full_frontend(src_provider, "provider", "provider", log)
        val src_consumer = "import provider\nfn main() -> i64:\n    provider.answer()"
        val consumer = parse_full_frontend(src_consumer, "consumer_rskp", "consumer_rskp", log)

        var modules: Dict<text, Module> = {}
        modules["provider"] = provider
        var sources: [SourceFile] = []
        sources = sources.push(SourceFile(path: "provider", content: src_provider, module_name: "provider"))
        val surfaces = match module_surfaces_from_modules(modules, sources):
            case Ok(v): v
            case Err(_): assert_true(false); ModuleSurfacesByName(surfaces: [], index_by_name: {})

        var lowering = hirlowering_for_module("consumer_rskp", surfaces)
        val hir = lowering.lower_module(consumer)
        expect(lowering.errors.len()).to_equal(0)

        for key in hir.symbols.symbols.keys():
            val candidate = hir.symbols.symbols[key]
            val cdisc = rt_enum_discriminant(candidate.kind)
            var fn_matched = false
            match candidate.kind:
                case SymbolKind.Function: fn_matched = true
                case _: fn_matched = false
            var mod_matched = false
            match candidate.kind:
                case SymbolKind.Module: mod_matched = true
                case _: mod_matched = false
            print("name={candidate.name} defining_module={candidate.defining_module} disc={cdisc} fn_matched={fn_matched} mod_matched={mod_matched}")
```

Actual output (`bin/simple test --no-session-daemon`, currently-deployed
`bin/release/x86_64-unknown-linux-gnu/simple`, which is the Rust bootstrap
seed per its own startup banner):

```
name=answer defining_module=Option::Some(provider) disc=-1 fn_matched=false mod_matched=false
name=provider defining_module=Option::Some(provider) disc=-1 fn_matched=false mod_matched=false
name=main defining_module=Option::Some(consumer_rskp) disc=-1 fn_matched=false mod_matched=false
```

`main` is defined in `consumer_rskp` and matched from code in the same
lowering call for `consumer_rskp` — not cross-module — and still shows
`disc=-1` / `fn_matched=false` for `SymbolKind.Function`. All three symbols
fail identically regardless of `defining_module`.

### Negative controls (root cause is NOT reproducible outside the real `HirLowering`/`SymbolTable` machinery)

Each of the following passed cleanly (`match`/`case` and `rt_enum_discriminant`
behave correctly), ruling out the corresponding hypothesis:

1. **Duplicate same-name enum across sibling modules** (the "interp struct
   name-collision global registry" family, `enum SymbolKind` really is
   declared with different variant orders in ≥6 files repo-wide: `hir_types.spl`,
   `90.tools/query_types.spl`, `00.common/dependency/symbol.spl`,
   `app/interpreter/collections/persistent_symbol_table.spl`, and both
   `lib/{nogc_sync_mut,nogc_async_mut}/dependency_tracker/symbol.spl`): three
   sibling `.spl` files (`lib_a`/`lib_b`/`lib_c`), each declaring its own
   `enum Shared` with a different variant order/name under the bare name
   `Shared`, construct-in-A/match-in-C after forcing B's conflicting
   declaration to load first — matched correctly (2 == 2). This DOES confirm
   the enum-registry collision family is real and present in this codebase
   (`named_type_register` in `10.frontend/core/types.spl:559` is a flat,
   name-keyed — not module-qualified — global array; MIR's
   `enum_variant_index: Dict<text,[text]>` in
   `50.mir/_MirLoweringExpr/switch_operators_calls.spl:62` is the same
   shape), but it is **not** what a small user-level program triggers under
   the currently-deployed engine.
2. **Symlinked-directory import-path aliasing** (`compiler.hir.X` vs
   `compiler.20.hir.X`, exactly the mechanism IMP2's code comment blames):
   replicated with a real symlink (`alias_lib -> real_lib`) and one enum
   declared in the target file, constructed via the real-path spelling,
   matched via the alias-path spelling — matched correctly.
3. **`Dict<i64, StructWithEnumField>` bracket-index round-trip in isolation**,
   single module, no class wrapping: matched correctly (though
   `rt_enum_discriminant` called directly as an extern from user `.spl` code
   returned a garbage-looking large int rather than a clean small index or
   -1 — that extern call is itself unreliable as a raw diagnostic from user
   code; the real `match`/`case` dispatch is the trustworthy signal, and it
   passed here).
4. **Same, widened to a 9-field struct shape matching `HirSymbol`** (leading
   `Option<text>` field, two enum-typed fields, matching `hir_types.spl:77`'s
   field list): matched correctly.
5. **Same, wrapped in a `class` with a `Dict<i64, Item>` field** (mirroring
   `class SymbolTable: symbols: Dict<i64, Symbol>`, two levels of
   class-field indirection matching `self.symbols.symbols[key]`): matched
   correctly.
6. **Import-spelling variation in the *consuming* spec** (`use
   compiler.hir.hir_types.{SymbolKind}` vs `use compiler.hir.hir_types.*`):
   no difference — both reproduce the failure identically.

None of these synthetic replicas — including ones that intentionally
recreate the symlink-alias mechanism, the struct shape, and the class/Dict
nesting depth — reproduce the corruption. It is specific to something in the
*real* `HirLowering`/`SymbolTable`/`module_lowering.spl` call graph (huge
transitive module count, the real `HirType?` field's actual shape/recursive
`HirTypeKind` enum, and/or `self.symbols.define`'s actual ID-allocation
logic) that a small isolated reproduction does not trigger. Not enough
budget remained this lane to instrument further inside that real call graph
(the prior lane, IMP2, also resorted to "in-place instrumentation, reverted"
rather than a standalone repro — consistent with this being hard to isolate
smaller).

## Classification

**Blocked on further runtime investigation** — this is very likely still in
the same general "structurally dead via pattern mismatch" family as:

- naked-struct-pattern-vs-Option always-wildcard
  (`naked_struct_pattern_vs_option_always_wildcard_2026-07-29.md`, lane SYM0)
- interp struct name-collision global registry (memory:
  `feedback_interp_struct_name_collision_global_registry`)
- Native Dict `.get()`/index corrupting struct/enum-valued entries (memory:
  `reference_native_dict_get_struct_corrupt_len_minus_one.md`)

but DISC1 could not pin the exact trigger down to a single, pure-Simple-fixable
site within this lane's budget — every synthetic isolation attempt (listed
above) came back green, so a confident scoped fix is not available yet. No
Rust/C runtime code was touched (per campaign rule: do not patch the seed
runtime without a nailed-down root cause). **No fix applied this lane.**

## Workaround (already landed, lane IMP2 — validated more broadly correct by DISC1)

Drop the kind filter; key on `(defining_module, name)` instead — local
variables/params never carry `defining_module`, so module-qualified callable
detection stays safe and falls through silently when no match exists.
Sites: `field_module_callable` and the MethodCall module-call check in
`expressions.spl` (both commented in-line). DISC1's `main`-symbol finding
means this workaround's justification is actually *broader* than originally
documented: `SymbolKind` pattern gates are unsafe on symbols from
`HirLowering.symbols.symbols` even when `defining_module` is the same module,
not only across a module boundary — so `(defining_module, name)` keying
should stay as the standing pattern everywhere `self.symbols.symbols[...]`
is read, not just at explicitly cross-module call sites.

## DISC1 supplementary fix: eliminated 2 of the real duplicate-name collisions found by control #1

Independently confirmed control #1's premise (`enum SymbolKind` really is
declared with ≥4 divergent variant orders across `hir_types.spl` (15
variants, `Module`@12), `90.tools/query_types.spl` (11 variants, `Module`@7),
`00.common/dependency/symbol.spl` (6 variants, `Module`@5), and the
byte-identical `app/interpreter/collections/persistent_symbol_table.spl`
duplicate) and that this collision family is real and *already fixed once
before* for `CompiledSymbolKind` (commit `3e92fc11511`, "align duplicate
CompiledSymbolKind so native-build resolves Const" — same "first-registration
wins in the global name-keyed registry" mechanism, same
`named_type_register`). Reproduced the identical *error signature* live
(`error: semantic: unknown variant or method 'Four' on enum Shared`) with a
fresh 3-file repro under `SIMPLE_EXECUTION_MODE=interpreter`, confirming the
registry-collapse mechanism is current and real — matching DISC1's control
#1 exactly.

**However**, per control #1's own conclusion this collision family is **not**
what the tracked `-1`/`fn_matched=false` symptom above is caused by: a
from-scratch isolated repro of `hir_types.SymbolKind` alone (single `use
compiler.hir.hir_types.{SymbolKind}`, immediate construct+match, zero other
`SymbolKind`-named imports in the file or its transitive closure) *still*
returns `-1` — so removing the other declarations' name collisions cannot be
the fix for this bug specifically. That isolated-hir_types repro's own
result is consistent with control #6 above (import-spelling doesn't matter,
still reproduces).

Applied anyway as an independent, low-risk hygiene fix (same pattern as the
`CompiledSymbolKind` precedent and the existing `DepSymbolTable` rename
already in this same file for the identical reason): renamed the two
genuinely-divergent non-canonical declarations so they can no longer collide
with `hir_types.SymbolKind` or each other by bare name:

- `src/compiler/90.tools/query_types.spl`: `enum SymbolKind` →
  `QuerySymbolKind` (11 variants unchanged). Updated the ~2 real consumers
  (`query_helpers.spl`, `query_api.spl`, both `use query_types.*`) and the
  `90.tools/__init__.spl` re-export.
- `src/compiler/00.common/dependency/symbol.spl`: `enum SymbolKind` →
  `DepSymbolKind` (6 variants unchanged; zero real consumers found outside
  its own struct field — `query_helpers.spl`/`query_api.spl` only import
  `DepSymbolTable` from this file, not `SymbolKind`). Updated the
  `00.common/dependency/__init__.spl` re-export. Added an in-file comment
  explaining the rename, matching the existing `DepSymbolTable` comment in
  the same file (which was renamed once before for the exact same reason).
- Left `persistent_symbol_table.spl`'s duplicate alone (byte-identical
  variant order to `hir_types.SymbolKind`, so the collision is harmless per
  the `CompiledSymbolKind` precedent's own reasoning) and left the
  `sffi_gen/specs/compiler_query.spl` copy alone (an SFFI codegen template,
  not `use`d by normal compilation — confirmed via repo-wide grep). The
  `lib/{nogc_sync_mut,nogc_async_mut}/dependency_tracker/symbol.spl` pair
  (yet another divergent shape, `Macro` not `MacroKind`) was left for a
  follow-up audit — out of this lane's verified blast radius.

Verified: `bin/simple lint` on all 6 touched files → 0 errors, 2 pre-existing
unrelated warnings. `bin/simple compile` on `query_api.spl` and
`dependency/symbol.spl` hits the *same* pre-existing, unrelated failures with
and without this change (confirmed by `git stash` A/B: `undefined identifier:
core_token_env_save_slot` in `query_api.spl`'s unrelated transitive deps;
"cannot compile to standalone SMF" for pattern-match-using functions in
`dependency/symbol.spl`'s package — neither mentions `SymbolKind`). Required
regressions: `qualified_import_call_spec.spl` 3/3 passed,
`resolve_import_symbols_spec.spl` 8/8 passed (both unaffected — neither
imports the renamed declarations).

**This fix does not touch the core tracked bug** (the `-1`/`fn_matched=false`
result inside real `HirLowering`/`SymbolTable` machinery) and does not
re-enable the `SymbolKind` filter in `field_module_callable` — per the
existing classification above, that remains blocked on further runtime
investigation.

## DISC2 update (2026-07-30): ROOT CAUSE NAILED — bare-name collision between `SymbolKind` variants and `parser_types.spl` struct names

Bisected by instrumenting directly inside `SymbolTable.define` in
`src/compiler/20.hir/hir_types.spl` (temporary `print(rt_enum_discriminant(...))`
calls, all reverted — file diffs clean against origin after this lane).

**First corrupting hop:** there is no hop — the value is already "corrupt"
(`rt_enum_discriminant == -1`, real `match`/`case` never fires) at the very
first point it can be observed: a **freshly-constructed local literal**,
e.g. `val fresh_local: SymbolKind = SymbolKind.Function` followed
immediately by `match fresh_local: case SymbolKind.Function: ...`, two
lines apart, inside `SymbolTable.define` itself — zero Dict round-trips,
zero struct/class wrapping, zero cross-function or cross-module boundary.
This falsifies every hypothesis in the previous update's "Fix direction"
(Dict round-trip, retrieval-time corruption, cross-module boundary): **the
bug is not about value flow at all.** It is a property of the `SymbolKind`
*type itself*, in the context of the real program, independent of how/where
a value of it is constructed or read.

**Mechanism, confirmed by a 6/6 controlled prediction test** (all run
in-place inside `hir_types.spl:SymbolTable.define`, same function, same
scope):

`compiler.frontend.parser_types.spl` declares **structs whose bare names
exactly match 11 of `SymbolKind`'s 15 variant names**: `Module`, `Import`,
`Function`, `TypeParam`, `Class`, `Struct`, `Enum`, `Field`, `Trait`,
`TypeAlias`, `Const` (verified via `grep -n '^struct ' parser_types.spl`).
The 4 non-colliding variants are `Method`, `Variable`, `Parameter`,
`EnumVariant` (parser_types.spl has `Param`, not `Parameter`, and `Variant`,
not `EnumVariant` — near-misses, not collisions). `hir_types.spl` and
`module_lowering.spl` both pull every one of these structs into scope via
`use compiler.frontend.parser_types.*` (glob import).

Prediction vs. observed result for `SymbolKind` variants, real `match`/`case`
and `rt_enum_discriminant`, all evaluated in the same function/scope:

| Variant | Colliding struct in parser_types.spl? | Predicted | Observed match `ok` | Observed `disc` |
|---|---|---|---|---|
| `Function` | yes (`struct Function`) | FAIL | false | -1 |
| `Module` | yes (`struct Module`) | FAIL | false | -1 |
| `TypeParam` | yes (`struct TypeParam`) | FAIL | false | -1 |
| `Struct` | yes (`struct Struct`) | FAIL | false | -1 |
| `EnumVariant` | no | WORK | true | 1582233792 |
| `Method` | no | WORK | true | 2509199419 |

6/6 correct. As an independent cross-check, `ScopeKind` (declared in the
same file as `SymbolKind`, sharing the variant names `Function`/`Module`/
`Class` with it) shows the identical failure for `ScopeKind.Function`
(`ok=false`, `disc=-1`) — the collision is keyed on the bare name, not on
`SymbolKind` specifically. Two enums that don't share any name with an
in-scope struct — `Visibility` (`Public`/`Peer`/`Up`/`Internal`/`Package`/
`Private`, no collision) and an isolated from-scratch 15-variant enum with
zero other declarations in its file — both discriminant *and* match/case
work correctly (`disc` is a plausible hash value, not `-1`; match succeeds),
which is why none of DISC1's negative controls (small isolated files with
no colliding struct in scope) ever reproduced it.

This is the **same defect family already documented** at
`hir_lowering/expressions.spl:416-426` ("SEED PATTERN HAZARD ... when a
variant pattern's name is ALSO a struct name in scope, the seed compiles the
`case ExprKind.Field(...)` TEST as a struct pattern = ALWAYS TRUE ...
`rt_enum_discriminant` = `DefaultHasher(variant name)` truncated to u32")
— but that comment describes the *payload-carrying* variant case, which
manifests as an **always-true** dead arm. `SymbolKind`'s colliding variants
are all *bare* (no payload), and the same underlying bare-name collision in
the seed's (Rust, `compiler_rust`) pattern/discriminant machinery manifests
here as **always-false** (`-1` is evidently a "name is ambiguous across
multiple registered declarations" sentinel in the seed's flat, non-type-
qualified name registry, distinct from a real — if collision-corrupted —
hash value). Same root registry, two different visible symptoms depending on
whether the colliding pattern carries a payload.

### Why no fix was applied this lane

A real fix is **not contained**: 11 of `SymbolKind`'s 15 variants collide.
Renaming `SymbolKind`'s variants, or renaming `parser_types.spl`'s 11
colliding structs, both have blast radius across dozens of `case
SymbolKind.X:` / `Function`/`Module`/`Class`/`Struct`/`Enum`/`Field`/
`Trait`/`TypeAlias`/`TypeParam`/`Const`/`Import` call sites throughout
`20.hir` and the whole frontend/parser — far beyond a single lane's safe,
verifiable scope. The alternative (fixing the seed's Rust pattern/
discriminant codegen to qualify by enclosing enum type instead of a flat
bare-name registry) is a `compiler_rust` runtime change, excluded by this
campaign's rule against patching the seed runtime without prior orchestrator
sign-off even now that the root cause is nailed down.

**Practical implication (unchanged, now precisely justified):** any `case
SymbolKind.X:` where `X` is one of `Function`, `Field`, `Class`, `Struct`,
`Enum`, `Trait`, `TypeAlias`, `TypeParam`, `Const`, `Module`, `Import`, in
any file that has `compiler.frontend.parser_types.*` (or an explicit import
of the colliding struct name) in scope, is a **dead arm that silently never
fires**. This is effectively "most `SymbolKind` pattern matches inside
`20.hir`" — an audit of other `case SymbolKind.` sites for this shape is
still open work for a future lane. IMP2's `(defining_module, name)`-keyed
workaround in `field_module_callable`/the `MethodCall` module-call check
(`expressions.spl`) must stay; it is the only verified-safe way to test
symbol identity in this code today.

## Fix direction (next lane)

1. **Audit**: grep `20.hir/**/*.spl` for `case SymbolKind\.(Function|Field|Class|Struct|Enum|Trait|TypeAlias|TypeParam|Const|Module|Import)` and treat every hit as a confirmed-dead arm needing the `(defining_module, name)`-style workaround (or an equivalent non-`.kind`-pattern-match rewrite) until the underlying seed bug is fixed.
2. **Real fix options** (both out of this lane's scope, need explicit sign-off before attempting): (a) seed `compiler_rust` codegen/pattern-matching fix to qualify bare-name enum-variant/struct resolution by the enclosing type instead of a flat global name table; (b) a coordinated, whole-codebase rename of either `SymbolKind`'s colliding variants or `parser_types.spl`'s colliding structs, verified file-by-file.
3. Do **not** re-attempt "isolated small repro" experiments for this family — the mechanism requires the colliding struct name to be in the same file/scope as the enum-variant pattern; a repro must deliberately include that colliding declaration (this is why DISC1's negative controls, which never included a same-named struct alongside the enum, came back green).

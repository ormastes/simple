# Stage-2 native codegen: `imported enum has no declaration owner` on a plain single-hop import

- Status: OPEN (2026-09-14)
- Lane: BOOT-20 (`work/bootstrap-s3-2-2026-09-14`)
- Binary: pinned Stage-2 candidate `bin/release/aarch64-unknown-linux-gnu/simple.phase2`
  (the boot18d `stage2/aarch64-unknown-linux-gnu/simple` artifact), sha256 `80911c47f07cdb64...`
  (short form used throughout the BOOT-18/19/20 lanes: `80911c47f07cdb64b4c3`)
- Class: native-codegen-only miscompile (Dict class field), workaround landed
  in `be66529a5f3` (`fix(hir): read imported enum owner from the symbol table,
  not a native-buggy class field`)

## Symptom

Receipt-free Stage 3 (`SIMPLE_BOOTSTRAP=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1
<stage2-candidate> native-build src/app/cli/bootstrap_main.spl ...`) fails
HIR lowering with:

```
error: focused native-build: HIR lowering error in src/app/cli/bootstrap_main.spl:
imported enum `EnumPatternPayload` / `DiagramGraphKind` / `CompileMode` /
`MarkdownBlock` / `UnaryOp` has no declaration owner
```

## Minimal reduction (measured 2026-09-14, ~1s native-build each)

Two files, no facade, no re-export, no sibling directory interference, enum
never even referenced in the importer's body:

`a.spl`:
```
enum Kind:
    Alpha
    Beta
```

`c.spl`:
```
use pkg.a.{Kind}

fn main():
    print("hi")
```

`SIMPLE_BOOTSTRAP=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 <stage2-candidate>
native-build c.spl -o out` fails:
`imported enum \`Kind\` has no declaration owner`, attributed to BOTH `c.spl`
and (when a re-export facade is inserted) the facade module itself.

Removing the facade, removing the match/usage of the enum, and moving the two
files into separate directories (to rule out directory-sibling
reprocessing, `resolve_package_sibling_symbols`) all leave the failure
unchanged. This is **not** a re-export-chase defect — the
`[hir-reexport-chase-unresolved]` lines that appear alongside it in the
Stage-3 log (chasing unrelated builtins through `std.nogc_sync_mut.spec`'s
facade chain, see the companion doc below) are unrelated noise for this
specific error.

## Discriminated: native-only, not a `.spl` logic bug

The exact same shape, run through the SAME `.spl` HIR-lowering source
in-process (calling `compiler.hir.hir_lowering.types.hirlowering_for_module`
+ `.lower_module(...)` directly, the technique
`test/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.spl`
already uses), interpreted by the Rust seed via `bin/simple run`:

```
errors.len=0
imported_enums.len=1
imported_enum_owners.len=1
```

Clean. Same logic, different engine (interpreted vs. natively compiled),
different result. (An earlier attempt to reproduce this in-process failed
with `missing importing module surface for boot20.consumer` — that was a
harness bug: the harness omitted the consumer module's own entry from the
`modules`/`sources` maps passed to `module_surfaces_from_modules`. Once the
consumer module is registered too, the fixture lowers clean. Anyone
re-chasing this: don't rediscover that dead end.)

## Root cause

`src/compiler/20.hir/hir_lowering/_Items/module_build.spl`,
`lower_module_enum_definitions` (pre-fix, ~line 165-178), reads the enum's
declaring-module name from `self.imported_enum_owners`, a
`{text: text}` (`Dict<text,text>`) **class field** of `HirLowering`,
written at `module_import_registration.spl:373`
(`self.imported_enum_owners[local_name] = imported_mod.module_name`) in the
same guarded block that writes the companion `imported_enums` field. Under
Stage-2 native codegen, this field's `contains_key`/bracket-read pair
silently misreports for this shape — the value was written, but the read
back does not see it (or sees corrupted data). Confirmed independently
(outside the compiler entirely) with a minimal probe:

```simple
struct EnumLike:
    tag: text

class Holder:
    enums: {text: EnumLike}
    owners: {text: text}

fn main():
    var h = Holder(enums: {}, owners: {})
    val k = "Kind"
    if not h.enums.contains_key(k):
        h.enums[k] = EnumLike(tag: "enum-payload")
        h.owners[k] = "mod_a"
    print("OWNER-PRESENT: " + h.owners[k])
```

Native-built by the Stage-2 candidate and run: prints
`OWNER-PRESENT: 200191203302897` — a raw undecoded word, not the text
`"mod_a"`. `contains_key` itself reports correctly (`true`) in this exact
probe; it is specifically the **bracket-read of a `text`-valued CLASS FIELD
Dict** that is corrupt. This is a new variant not covered by
`doc/07_guide/language/dict_native_pitfalls.md`'s existing truth table
(which documents array-valued class-field bracket-read SEGVs, not
text-valued garbage reads on a hit).

A related but distinct native defect in the same family: moving the
write (`self.<dict>[k] = v` inside a guarded `if` block) into a class
**method** — rather than inline in `fn main()` — makes the Stage-2
candidate **SEGV while compiling** the probe program (during its own MIR
lowering), even for a SINGLE dict-field write, not just the dual
enums+owners write. See the companion bug doc
`stage2_native_method_scoped_dict_field_write_segfaults_2026-09-14.md`.

## Fix (workaround, not a root-cause fix)

`imported_enum_owners` is never read again for this decision.
`lower_module_enum_definitions` now calls a new helper,
`imported_enum_owner_module(local_name)`, that reads the owner back from
`HirSymbol.defining_module` — already recorded at the exact same
registration call site
(`self.symbols.define(local_name, SymbolKind.Enum, ..., Some(imported_mod.module_name))`)
— using the scalar-safe `lookup_or_invalid` -> `self.symbols.symbols.has(id)`
-> bracket-read -> `?? ""` pattern `claim_materialized_payload_binding`
already relies on for exactly this class of native Dict hazard.
`imported_enum_owners` the field, its write, and its per-module reset are
all left in place (unused for this decision) because two other specs pin
its literal source shape and reset contract:
`test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl`
and `test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl`.
Deleting the field would need updating both; reading around the bug instead
touches only the one call site that was actually broken.

Landed: `be66529a5f3` (`fix(hir): read imported enum owner from the symbol
table, not a native-buggy class field`), `work/bootstrap-s3-2-2026-09-14`.

## Verification

- RED (pre-fix): `SIMPLE_BOOTSTRAP=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1
  <old stage2 candidate, sha 80911c47f07cdb64b4c3> native-build c.spl -o out`
  → `imported enum \`Kind\` has no declaration owner`.
- GREEN (seed, contract pin): `test/01_unit/compiler/hir/imported_enum_owner_native_workaround_spec.spl`
  passes under `bin/simple test` (interpreted).
- GREEN (native, post-fix): pending a rebuilt Stage-2 candidate from this
  fix — see the BOOT-20 receipt for the rebuild outcome.

## Related

- `doc/08_tracking/bug/phase2_stage2_spec_framework_unresolved_reexport_chase_2026-09-13.md`
  — a DIFFERENT root cause (multi-hop re-export chase through
  `std.nogc_sync_mut.spec`), filed by a sibling lane; do not conflate the two.
  That doc's own recommendation ("reproduce narrowly with a 3-file minimal
  facade chain... to isolate whether the break is at the enum-import step
  specifically or the generic multi-hop facade chase") is answered by this
  doc: it is neither — it is a native Dict class-field defect, present even
  with zero facade hops.
- `doc/07_guide/language/dict_native_pitfalls.md` — existing truth table;
  this bug is a new row (class-field `text`-valued bracket-read garbage on a
  hit), not yet added there pending wider confirmation.

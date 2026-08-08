# MIR qualified struct-field key namespace mismatch: b9e23914a0e's new tier cannot fire across an import

**Date:** 2026-08-08
**Status:** OPEN
**Severity:** High (the landed fix is plausibly a NO-OP on the case it claims to fix)
**Area:** `src/compiler/50.mir`, `src/compiler/20.hir`
**Relates to:** `b9e23914a0e`, and the diagnosis chain
`09e85f624ec` -> `61197205501` -> `1d1267788e6` -> `55902d491f8`
(`doc/08_tracking/bug/stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`)

Adversarial review of the landed resolution cluster. Findings ranked
most-severe-first. Confidence is stated per finding; nothing here is claimed
green, and the one test that would settle Finding 1 is named explicitly as
un-run.

---

## Finding 1 (HEADLINE) — the qualified key is built from TWO DIFFERENT
## namespaces on the producer and consumer sides, so the new tier misses
## across a module import

**Confidence: CONFIRMED by static inspection of both assignment sites.**
Not yet confirmed dynamically (see "What would settle this").

`b9e23914a0e` adds a "module-qualified name tier FIRST" to
`MirLowering.resolve_field_index`
(`src/compiler/50.mir/_MirLowering/function_lowering.spl`, ~line 953). It is
gated on:

```
val q_type_symbol = self.symbols.get_symbol_raw(found_type_sym.id)
if q_type_symbol != nil:
    val qualified_key = self.composite_layout_key(q_type_symbol)
    if qualified_key != q_type_symbol.name and self.struct_field_order.has(qualified_key):
```

`composite_layout_key` (`50.mir/_MirLowering/module_lowering.spl:192`) builds
`"{symbol.defining_module}::{symbol.name}"`. So the tier fires only when the
consumer-side `defining_module` string is **byte-identical** to the
producer-side one used when the layout was registered. It is not.

**Producer side — declaration.** `declare_module_types`
(`20.hir/hir_lowering/_Items/module_lowering.spl:2354`):

```
# Pass module filename for visibility tracking
val mod_name = if self.module_filename != "": Some(self.module_filename) else: nil
...
self.symbols.define(name, SymbolKind.Class, nil, decl_span, decl_visibility, false, mod_name)
```

`module_filename` is a **repo-relative FILE PATH**. Its declaration says so
(`20.hir/hir_lowering/types.spl:68`:
`module_filename: text  # Filename/path for visibility matching and defining_module population`),
it is assigned from `filename` (`types.spl:248/254/281/311/321`), and it is
compared against a literal path elsewhere (`types.spl:390`:
`self.module_filename == "src/lib/nogc_async_mut/async/future.spl"`).

MIR registers the qualified `struct_field_order` key from exactly these
symbols — `module_lowering.spl:719-735` (local, `overwrite: true`) and
`:656-672` (cross-module prescan) both do
`module.symbols.get_symbol_raw(class_def.symbol.id)` then
`self.composite_layout_key(class_symbol)`. So every registered qualified key
has the shape:

```
src/compiler/55.borrow/nll.spl::NLLChecker
```

**Consumer side — import.** `register_imported_symbol`
(`20.hir/hir_lowering/_Items/module_lowering.spl:743`):

```
val imported_type = self.symbols.define(local_name, kind, nil, import_span,
                        Visibility.Public, false, Some(imported_mod.module_name))
```

`ModuleSurface.module_name` is populated from `source.module_name`
(`20.hir/hir_lowering/module_surface.spl:933`), and `ModuleSurface` carries
`canonical_path` as a *separate* field on the very next line — the two are
deliberately distinct. `SourceFile.module_name` is the **dotted logical
module name** (`_driver_module_name_from_path`, and
`hir_pkg_canonical_module_name` in `module_surface.spl:83` which drops
all-digit tier segments). So the key the consumer computes has the shape:

```
compiler.borrow.nll::NLLChecker
```

**Consequence.** `self.struct_field_order.has(qualified_key)` is FALSE for
every imported type, the new tier is silently skipped, and control falls
straight through to the collided id-keyed `field_map` tier — returning the
same wrong index as before the fix.

### Concrete failure scenario (the cluster's own case)

`src/compiler/55.borrow/mod.spl` reads `nll.errors`, where `NLLChecker` is
defined in a different module (`nll.spl`) and reaches `mod.spl` via an
import.

1. Prescan/local registration stores `src/compiler/55.borrow/nll.spl::NLLChecker`
   -> `[..., errors at index 4]` (offset `0x20`).
2. While lowering `mod.spl`, `expr_type_symbol(base)` yields the *imported*
   `NLLChecker` symbol, whose `defining_module` is `compiler.borrow.nll`.
3. `composite_layout_key` -> `compiler.borrow.nll::NLLChecker`.
4. `struct_field_order.has(...)` -> **false**. Tier skipped.
5. Falls through to `field_map[sym_id]`, which the cluster's own diagnosis
   says is poisoned by `MirLowering`'s entry (both classes have an `errors`
   field) -> index 11 -> `mov 0x58(%r15),%rdi` -> the SIGSEGV, unchanged.

Note the tier *does* work for a **locally-defined** type: there, both sides
use the same `module.symbols` symbol, so both strings are the file path and
they match. But that is precisely the case the fix was not needed for —
`module_lowering.spl:719/730` already re-registers the module being lowered
with `overwrite: true` ("The module being lowered is authoritative for its
own same-name struct/class"), so the bare tier is already correct there.

**Net: the new tier fires where it was not needed and is skipped where it
was.** The commit message's claim that this is the stage3 SIGSEGV root-cause
fix is not supported. The commit is honest that "Full stage-3 SIGSEGV retest
pending" — this finding predicts that retest will still be RED.

### What would settle this

A dynamic probe printing `qualified_key` and the `has()` result on the first
`resolve_field_index` call for an imported type. NOT RUN here: it requires a
stage-2 rebuild (measured at 908 MB / 167.7 s by `1d1267788e6`), and per that
same commit a stage-2-only build is **structurally blind** to `src/compiler`
changes because `build_stage2.sh` sets `SIMPLE_NATIVE_BUILD_RUST=1`. A real
verification needs a full Stage 3. Stated as unverifiable-here rather than
guessed either way.

### Suggested fix direction (not landed — unproven)

Make both sides agree on one namespace. Either normalize `defining_module`
through a single canonicalizer at both `:743` and `:2354`, or have
`composite_layout_key` normalize (e.g. via
`hir_module_logical_name_from_path`) so a path and a dotted name collapse to
the same key. Do not land without the dynamic probe above.

---

## Finding 2 — the construction path is still bare-name keyed, so the read
## path and the write path can now disagree

**Confidence: CONFIRMED (code inspection); the divergence it enables is
CONDITIONAL — see the condition below.**

`lower_struct_construct`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:3038`)
receives a `symbol: SymbolId` and **ignores it**, keying by the bare name:

```
me lower_struct_construct(symbol: SymbolId, struct_name: text, args: [HirCallArg]) -> LocalId:
    val field_names = self.struct_field_order[struct_name]
```

`b9e23914a0e` qualified the READ path only. The fix is therefore partial by
construction: field *writes* are laid out from the bare, collision-prone key
while field *reads* may now be resolved from the qualified key.

**Condition under which this bites.** It does NOT bite for a type defined in
the module being lowered — `module_lowering.spl:719/730` re-registers that
module's own composites with `overwrite: true`, so the bare key holds the
current module's layout and both paths agree. It requires an **imported**
same-named type, where the bare key holds a foreign (first-wins prescan or
local) layout while the qualified key resolves to the defining module's.

**Concrete failure scenario.** `mod_a` and `mod_b` each declare
`class Config`; `mod_a::Config = [alpha, beta, errors]`,
`mod_b::Config = [errors, gamma]`. `mod_c` imports `mod_b`'s `Config` and
does `val c = Config(errors: e, gamma: g)` then reads `c.errors`.

- Construction uses `struct_field_order["Config"]`. While lowering `mod_c`,
  that bare key holds whatever won the prescan — `mod_a`'s 3-field list, say
  — so `errors` is written to slot 2 and `gamma` gets a nil fill.
- The read `c.errors` goes through the new qualified tier and, if Finding 1's
  namespace mismatch is fixed, resolves `mod_b::Config` -> index 0 -> reads
  slot 0 (`alpha`'s slot, nil/garbage).

Before `b9e23914a0e` both paths were consistently wrong-but-matching (both
index 2). **Fixing Finding 1 without also qualifying the construction path
would convert a latent collision into an active construct/read mismatch.**
The two must land together.

---

## Finding 3 — the regression spec cannot reproduce the collision it claims
## to guard

**Confidence: CONFIRMED.**

`test/01_unit/compiler/mir/struct_field_order_module_qualified_spec.spl`,
4th example ("resolve_field_index prefers the qualified tier over a collided
field_map hit"):

```
val sym_a = symbols.define("Config", SymbolKind.Class, nil, empty_span(), Visibility.Public, false, Some("mod_a"))
...
fm[sym_a.id] = ["errors", "gamma"]     # poison field_map only
```

Two representativeness gaps:

1. **Only one of the two maps is poisoned.** `field_map` (`Dict<i64,[text]>`,
   `mir_lowering_types.spl:42`) and the symbol table (`Dict<i64,HirSymbol>`,
   reached by `get_symbol_raw`) are keyed by the *same* raw i64 and populated
   from the same per-module table. The fixture poisons `field_map` while
   leaving the symbol table pristine, so `get_symbol_raw(sym_a.id)` returns
   the correct `mod_a` symbol. A real entry-closure collision does not offer
   that guarantee.
2. **Producer and consumer strings are made identical by hand.** The fixture
   registers `"mod_a::Config"` and defines the symbol with
   `Some("mod_a")` — the same literal on both sides. That is exactly the
   coincidence that Finding 1 says does not occur in a real build, where one
   side is a path and the other a dotted name. The spec is green *because* it
   sidesteps the defect.

The commit message's positive control ("sabotaging the qualified tier flips
the poisoned-field_map case to FAIL") therefore proves only that the tier is
*consulted*, not that it *fires* in an entry-closure build. This is the
repo's documented fixture-only-detection pattern.

---

## Claims assessed and NOT found defective

- **Claim 2 (stage-2 byte identity does not prove pure-Simple attribution).**
  The self-correction IS present in the tree and is not reintroduced later.
  `1d1267788e6` explicitly corrects `61197205501`, and `55902d491f8` converts
  the remaining inference to direct evidence via PROBE3 (unconditional trace,
  positive control `QUUXMARKER`, `/proc/<pid>/environ` check, 0 trace lines
  across a 727-file compile). No later commit in the cluster reasserts the bad
  inference. This chain is honest and self-correcting; no finding.

- **Claim 4 (`si_addr` is derived, so `0x98` and `0x118` are one bug).**
  `09e85f624ec` states the derivation `(value & ~7) + 8` and explicitly says
  "one bug, not two". No surviving two-bug framing was found in the cluster.
  No finding.

- **The warn-once conflict diagnostic** (`module_lowering.spl`, new block) is
  correct as written: it compares field lists element-wise, stays silent on
  identical re-registration, exempts `::`-qualified keys, and is one-shot per
  bare name. It is a diagnostic only and changes no indices.

---

## Claim assessed as STILL OPEN

- **Claim 3, second defect: the borrow checker emits spurious errors on
  trivial code.** `61197205501` correctly identifies that the bad `0x58` read
  is reachable *only* on the Errors branch — i.e. `nll.check()` returned
  falsey on hello-world — so fixing the field offset yields a diagnostic
  failure, not `rc=0`. **Nothing in this cluster touches borrow check.**
  `b9e23914a0e` is confined to `50.mir`; the other four commits are
  docs-only. This defect is UNADDRESSED and remains open. Any future
  verification must assert "no SIGSEGV **and** hello-world compiles clean",
  not merely "no SIGSEGV".

---

## Method notes

- All five commits verified as ancestors of `origin/main`.
- Four of the five (`09e85f624ec`, `61197205501`, `1d1267788e6`,
  `55902d491f8`) are **docs-only** — single-file edits to
  `stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`. Only
  `b9e23914a0e` changes code.
- Enumeration done against `origin/main` blobs (`git show origin/main:<path>`),
  never the working copy, which carries in-flight edits from parallel
  sessions. Counts used `/usr/bin/grep`, not the `.gitignore`-honouring
  wrapper.
- **No positive control was run for Findings 1-3.** Each is a static-inspection
  finding about key derivation, and the only oracle that could settle Finding 1
  is a full Stage-3 build, which the stage-2 lane is structurally blind to
  (`1d1267788e6`). No green and no red is claimed from a build here.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>

# MIR qualified struct-field key namespace mismatch: b9e23914a0e's new tier cannot fire across an import

**Date:** 2026-08-08
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
this doc
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

### The consumer-symbol link is CONFIRMED, not inferred

Step 2 above ("the imported symbol reaches `resolve_field_index`") was
challenged in review as the one inferred link in an otherwise
inspection-confirmed chain. It checks out:

- `expr_type_symbol` (`50.mir/_MirLowering/function_lowering.spl:1097`) does
  nothing but read the annotation: `match ty.kind: case Named(symbol, _): Some(symbol)`.
  So the whole question is which symbol semantic lowering stamped into that
  `Named`.
- For an imported type, that is `imported_surface_type`
  (`20.hir/hir_lowering/_Items/module_lowering.spl:451-457`):
  `self.symbols.lookup_qualified_type_raw(imported_mod.module_name, source_name)`
  -> `HirTypeKind.Named(SymbolId(id: raw_symbol_id), [])`.
- That qualified binding is exactly the one established at `:745`,
  `bind_qualified_type(imported_mod.module_name, imported_name, imported_type)`,
  where `imported_type` is the symbol defined two lines earlier at `:743`
  with `defining_module = Some(imported_mod.module_name)` -- the **dotted**
  name.
- `rename_symbol` (`20.hir/hir_types.spl:517`) preserves `defining_module`
  verbatim, so the rename on the next line does not restore the path form.

So the `Named` carried by an imported-type expression resolves to the
CONSUMER's import symbol, whose `defining_module` is the dotted module name,
never the defining module's file path. The alternative -- that `Named` carries
the defining module's own symbol, which would have made the tier hit and
collapsed this finding -- is ruled out.

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

---

## Re-confirmed 2026-08-09

Re-read in full; status re-confirmed as ARCHITECTURAL-OPEN, not fixable in a
scoped pass. `struct_value_syms` and `module_lowering.spl` (two of the files
this document names as part of the fix surface) currently carry uncommitted
edits from a concurrent session in this shared working copy and were
explicitly out of scope to touch here regardless. Blocker A (no oracle for a
`src/compiler` source change short of a full Stage 3 rebuild) and Blocker B
(the transitive closure is ~340 references across 10+ interlocking bare-keyed
maps, a design-sized unit of work) both still hold on inspection of the
current tree; nothing in `50.mir` or `20.hir` has changed the namespace
derivation since this doc's last update. Left OPEN, no code changed for this
finding.

---

## DYNAMIC CONFIRMATION (2026-08-08) — the first actual measurement

The review above stated its central claim was static-only and named the probe
that would settle it. That probe has now been RUN, on the deployed
self-hosted binary (`bin/release/x86_64-unknown-linux-gnu/simple`,
`native-build` -> real ELF, executed). **Finding 1 and Finding 2 are both
CONFIRMED DYNAMICALLY.** No stage-3 was needed: a three-module program
reproduces the defect in ~110 s.

### The probe

```
# wallq_mod_a.spl
class Config:            # [alpha, beta, errors]
    alpha: i64
    beta: i64
    errors: i64
fn a_make() -> Config: Config(alpha: 111, beta: 222, errors: 333)

# wallq_mod_b.spl
class Config:            # [errors, gamma]   <-- SAME bare name, DIFFERENT layout
    errors: i64
    gamma: i64
fn b_make() -> Config: Config(errors: 777, gamma: 888)

# wallq_main.spl
use wallq_mod_a.{a_make}
use wallq_mod_b.{Config, b_make}
fn main():
    val c = Config(errors: 777, gamma: 888)   # constructed in the IMPORTER
    print("direct.errors={c.errors} expect=777")
    print("direct.gamma={c.gamma} expect=888")
    print("DISCRIMINATOR c.alpha={c.alpha}")  # alpha exists ONLY in mod_a
    val d = b_make()                          # constructed in its OWN module
    print("viafn.errors={d.errors} expect=777")
    print("viafn.gamma={d.gamma} expect=888")
    val e = a_make()
    print("a.errors={e.errors} expect=333")
```

Build note (cost the first attempt): `native-build` resolves
`src/runtime/runtime.c` relative to CWD, so the probe tree needs a
`src/runtime` symlink to the repo's. Without it the run ends
`error: LLVM native linking failed: ... Expected src/runtime/runtime.c` —
and the outer wrapper still reports `RC=0`, the known silent-failure shape.

### Measured output

```
direct.errors=777 expect=777        OK
direct.gamma=0   expect=888         *** WRONG ***
DISCRIMINATOR c.alpha=0             *** COMPILES AND RUNS ***
viafn.errors=777 expect=777         OK
viafn.gamma=888 expect=888          OK
a.errors=333    expect=333          OK
```

### What each line proves

1. **`c.alpha` compiles and runs at all.** `alpha` exists ONLY in
   `mod_a::Config`. `wallq_main` imports `mod_b`'s `Config` and never names
   `mod_a::Config`. That the field resolves is direct proof that the bare
   `Config` key in `struct_field_order` holds **mod_a's** layout while the
   consumer believes it holds mod_b's. The cross-module field-index
   collision is REAL and is not confined to entry-closure/bootstrap builds —
   it reproduces in an ordinary three-file `native-build`.

2. **`direct.gamma=0` vs `viafn.gamma=888` is the predicted local-vs-imported
   split, exactly.** `b_make` constructs inside `mod_b`, where
   `module_lowering.spl:719/730`'s `overwrite: true` re-registration makes
   the bare key mod_b's own layout — correct. The identical construction in
   the importing module gets mod_a's layout — wrong. This is precisely the
   asymmetry Finding 1 predicted ("the new tier fires where it was not needed
   and is skipped where it was").

3. **`direct.errors=777` is correct BY ACCIDENT, and that is the important
   part.** Construction and read are *both* keyed by the same bare name, so
   they are both wrong in the *same* direction and cancel. This is the
   empirical form of the sequencing hazard in Finding 2: today's state is
   **collided but CONSISTENT**. Fixing the READ path alone would move
   `errors` onto mod_b's index while construction still wrote it at mod_a's
   — turning a currently-correct read into a wrong one. **Any fix that
   qualifies the read path without qualifying construction makes this program
   strictly worse.** Confirmed, not merely argued.

4. **`gamma` was silently DROPPED at construction.** With field order
   `[alpha, beta, errors]`, the named arg `gamma: 888` matches no declared
   field, is inserted into `named_args` and never consumed, and no diagnostic
   is emitted — the Finding-3 named-constructor defect, observed. `alpha` and
   `beta` take the nil fill, which is why both `c.gamma` and `c.alpha` read
   as 0.

### This is now a cheap, permanent fix oracle

`direct.gamma` must become **888** once the namespace and the construction
path agree. Runtime ~110 s. Note that `c.alpha` resolving at all will NOT be
fixed by this work and must not be used as an oracle: `resolve_field_index`
returns index 0 on a miss and never errors, so nothing in the layout-key
change adds field-existence checking. `c.alpha` compiling is a SEPARATE
missing-validation defect (the same family as the dropped `gamma:` named
arg); it is diagnostic evidence here, not a target. This replaces "requires a full
Stage 3" as the verification bar for this bug: Stage 3 is still the
integration oracle, but it is no longer the *only* oracle.

## Correction to the "Suggested fix direction" — it is NOT a one-line change

The suggestion above ("normalize `defining_module` through a single
canonicalizer at both sites, or have `composite_layout_key` normalize") is
necessary but **not sufficient**, and landing only that half is the actively
harmful state proven by point 3.

Normalizing in `composite_layout_key` is the right shape and the right place
(`defining_module` is load-bearing elsewhere — 20.hir visibility matching
compares it against literal PATHS — so the two population sites must not
change). The canonical namespace should be the **dotted logical name**, not
the path, because `src/compiler` exposes each layer under both a numbered
real directory (`50.mir/`) and a symlink (`mir/`): one module, two path
spellings, one dotted name. `hir_pkg_canonical_module_name`'s rules (drop
all-digit tier segments, fold `std.` -> `lib.`) are exactly right and should
be reimplemented locally in 50.mir rather than imported, matching the
existing precedent in `bootstrap_globals.spl:57` and
`hir_module_logical_name_from_path`'s own docstring.

**Read the BLOCKER section below before starting.** It is the reason the
one-line normalization must NOT be landed by itself, and it names the real
scope (`struct_value_syms` re-namespacing across all writers and readers).
A lane that skips it will re-derive the same dead end.

Two further requirements that were not previously identified:

- **`canonical_mir_type_symbol` (`50.mir/_MirLowering/module_lowering.spl:198`)
  has the SAME two-namespace bug**, keying `"{defining_module}.{name}"`
  inline. Un-normalized, one physical type reached via declaration vs via
  import mints TWO distinct canonical MIR type symbols — defeating the exact
  canonicalization that function exists to provide. Same normalizer, same
  commit.

- **The conflict-warning exemption becomes unsound.**
  `register_composite_field_metadata:590` skips the divergent-field-list
  warning for any key containing `::`, on the premise that qualified keys
  "never collide". Normalization weakens that premise: dropping tier segments
  and folding `std.`->`lib.` could merge two genuinely distinct modules onto
  one key, after which `overwrite: false` first-wins hands the qualified tier
  a *confidently* wrong layout — worse than the ambiguous bare key. The
  exemption must be relaxed so qualified keys warn too; it is the only canary
  for a normalizer over-merge available without a full build.

## BLOCKER on the construction half — why this is still OPEN

`lower_struct_construct` cannot simply be re-keyed. Beyond the layout maps
(`struct_field_order`, `struct_field_hir_type`, `struct_field_type_name`,
`struct_field_has_default`, `struct_field_default_expr`), it writes the
constructed local's provenance into **`struct_value_syms`**, and
`resolve_field_index:1018` consults `struct_value_syms` as **tier 1 — BEFORE
the module-qualified tier**. So if construction keeps recording the bare
name, tier 1 returns the collided layout and the qualified tier is never
reached for any construct-then-read local: the read-path fix is defeated for
the dominant case.

But `struct_value_syms` cannot be qualified in `lower_struct_construct`
alone. It is written from at least six other sites with **bare** names —
`function_lowering.spl:296/328/330` (`parameter_type.name`),
`expr_dispatch.spl:229` (`struct_symbol_raw.name`), `expr_dispatch.spl:390`
(`nested_name`) — and read by consumers beyond field resolution, including
method dispatch (`module_lowering.spl:934`) and `expr_dispatch.spl:776`.
Qualifying one writer would leave the map holding two namespaces and would
plausibly break method dispatch — reintroducing, one layer down, the very
class of bug this document is about.

**A correct fix therefore has to re-namespace `struct_value_syms` across all
of its writers and readers in one change.** That is materially larger than
the read-path patch, and it has no oracle short of a compiler rebuild:
`src/compiler/**.spl` edits are NOT live for `native-build` (the deployed
binary is used), so the probe above cannot validate a source change until the
compiler is rebuilt. Scoping it correctly, rather than landing the harmful
half, is the reason this stays OPEN.

**Status: root cause CONFIRMED DYNAMICALLY; fix NOT LANDED.** A prepared
patch covering the normalizer, `composite_layout_key`,
`canonical_mir_type_symbol`, and the warning exemption exists but is
deliberately withheld, because on its own it is the read-path-only change
that point 3 proves is worse than the status quo.

---

## SCOPE RE-DERIVATION (2026-08-08, second lane) — the re-namespacing is
## NOT LANDABLE, and the reason is now two enumerated blockers, not an estimate

A follow-up lane was tasked with landing the `struct_value_syms`
re-namespacing in one commit. It re-derived the scope and the oracle from
`origin/main` blobs (`git show origin/main:<path>`, `/usr/bin/grep`, never the
working copy — the WC did not even contain this file, while `origin/main` did).
**It landed no code.** Today's collided-but-CONSISTENT state is intact. The two
blockers below are why, and both are corrections to the BLOCKER section above.

### Blocker A — there is NO oracle for a `src/compiler` source change

The BLOCKER section already noted this in passing; it is the decisive fact and
is restated here as a gate. The `direct.gamma` probe validates the **deployed
binary** (`bin/release/x86_64-unknown-linux-gnu/simple`), which is a compiled
ELF. A `50.mir/**.spl` edit cannot affect it. Confirmed negatively: a sweep of
`SIMPLE_*` env names across `src/app/build` and `src/compiler/80.driver` finds
**no** source-root / compiler-root override — there is no flag that makes
`native-build` consult compiler sources instead of its own compiled code.

So RED->GREEN->RED on the probe requires a self-hosted rebuild from modified
source. A stage-2-only build cannot serve: `SIMPLE_NATIVE_BUILD_RUST=1`
(`scripts/bootstrap/bootstrap-from-scratch.sh:1513/1565`) makes it structurally
blind to `src/compiler` changes. That leaves a full Stage 3 — which is exactly
the bar this document's DYNAMIC CONFIRMATION section was celebrating having
escaped. **The cheap oracle is an oracle for the defect, not for the fix.**
That distinction was not drawn before and is the trap for the next lane.

### Blocker B — the real surface is ~3x larger, and part of it carries no symbol

Re-derived counts (`src/compiler`, `origin/main` blobs):

| map | refs |
|---|---|
| `struct_value_syms` | **115** (13 files; 6 are prose-only in `20.hir`) |
| `struct_field_order` | 67 |
| `array_element_struct_syms` | 41 |
| `struct_method_syms` | 31 |
| `struct_field_type_name` | 27 |
| `struct_field_hir_type` | 15 |
| `struct_method_return_names` | 11 |
| `struct_field_array_element_type_name` | 9 |
| `struct_field_has_default` | 8 |
| `struct_field_default_expr` | 7 |

`struct_value_syms` alone: **24 writer sites** (not the "six other writers"
stated above) and **~30 real reader sites**, across 7 files in `50.mir`
(`_MirLowering/function_lowering.spl`, `_MirLowering/module_lowering.spl`,
`_MirLoweringExpr/expr_dispatch.spl`, `_MirLoweringExpr/literals.spl`,
`_MirLoweringExpr/method_calls_literals.spl`,
`_MirLoweringExpr/switch_operators_calls.spl`, `mir_lowering_stmts.spl`,
plus the field decl in `mir_lowering_types.spl:130`).

**The blocking part is not the count — it is that many writers have no symbol
to qualify FROM.** Spot-checked four:

- `function_lowering.spl:296/328/330` — value is `parameter_type.name`, and
  `parameter_type` IS `self.symbols.get_symbol_raw(type_symbol.id)`. **This one
  is qualifiable.** (Correction: the BLOCKER section listed it among the
  problem sites.)
- `expr_dispatch.spl:390` — value is `nested_name`, read out of
  `struct_field_type_name[name][field_idx]`: a plain field-type-name **string**
  from another bare-keyed map. No symbol exists at this point.
- `expr_dispatch.spl:1107` — value is `dict_struct_name`, which falls back to
  `array_element_struct_syms.get(base_local.id)`: again a bare-keyed text map.
  No symbol.
- `switch_operators_calls.spl:2328` — value is `payload_struct`, from
  `enum_payload_struct_names.get(payload_key)` (`:2264`), keyed
  `"{enum_name}::{variant}"`. No symbol.

So qualifying `struct_value_syms` is **not a mechanical rename**. Its values are
sourced from, and flow back into, a lattice of other bare-name-keyed text maps
(`struct_field_type_name`, `array_element_struct_syms`,
`struct_field_array_element_type_name`, `enum_payload_struct_names`,
`struct_method_syms`, `struct_method_return_names`). Qualifying one namespace
while the others stay bare recreates the two-namespace bug one layer down —
the precise failure mode this whole document is about. The transitive closure is
**~340 references across 10+ interlocking maps**, and closing it requires
*threading module provenance into paths that do not currently carry any*, which
is a design change, not a re-keying.

### Consequence for sequencing

Blocker B says the change is a design-sized unit of work. Blocker A says that
unit of work has no verification short of a full Stage 3. The task's own rule
applies: a partial landing here is *actively harmful* (point 3 above proves it),
so a change that cannot be completed AND verified in one commit must not be
started. **Nothing was landed.**

### The named-constructor Nil defect — DEFERRED, explicitly

Point 4 above observed `gamma: 888` being silently dropped at construction
(`lower_nil_expr` fills the slot with `ConstInt { value: 3 }`). Adding an
`error_fatal` there was reconsidered on the premise that a build oracle now
exists. It does not — see Blocker A: the oracle cannot observe a compiler-source
change. The original reason for withholding therefore stands unchanged: an
`error_fatal` on an unmatched named arg would convert a silent miscompile into
an undiagnosable bootstrap failure, with no way to demonstrate RED->GREEN first.
**Decision: not fixed, deliberately.** It should be landed together with the
re-namespacing, behind a real Stage-3 oracle.

### What the next lane actually needs first

Not more static scoping — that is now done. It needs **a compiler-source oracle
cheaper than a full Stage 3**. Until one exists, this bug stays OPEN by design,
and the correct action on it is to land nothing.

## Re-confirmed 2026-08-10

Fresh pass over this doc. `git status` shows every file in this doc's namespace
chain currently modified in this shared working copy
(`src/compiler/50.mir/_MirLowering/module_lowering.spl`,
`src/compiler/50.mir/_MirLoweringExpr/{expr_dispatch,switch_operators_calls}.spl`,
`src/compiler/50.mir/mir_data.spl`,
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`) — another
session is actively working this exact area right now. Two independent
reasons not to touch code in this pass: (1)
`src/compiler/50.mir/_MirLowering/module_lowering.spl` is explicitly
off-limits for this session (another session owns it), and it is the file
Finding 1's root cause lives in; (2) editing any of the other listed files
while they carry uncommitted concurrent changes risks clobbering that
session's in-flight work, per this repo's own shared-WC lore. No code
changed. **Classification: ARCHITECTURAL/OUT-OF-SCOPE for this pass** —
blocked by (a) a forbidden file and (b) live concurrent ownership of every
other file in the fix path, not by any new technical finding. The doc's own
prior conclusion ("land nothing until a compiler-source oracle exists")
still holds independently.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
Co-Authored-By: Claude Sonnet 5 <noreply@anthropic.com>


## 2026-08-17 CORE-P1 triage: DID NOT REPRODUCE / fix present in current source

Verified against CURRENT SOURCE (content, not SHA ancestry) during the crit_01
CORE-P1 sweep. Producer and consumer now agree. Consumer: `src/compiler/50.mir/_MirLowering/function_lowering.spl:1138-1140` consumes the QUALIFIED key first -- `val qualified_key = self.composite_layout_key(q_type_symbol)` then `if qualified_key != q_type_symbol.name and self.struct_field_order.has(qualified_key):`. Producer: `module_lowering.spl:780` (`val struct_key = self.composite_layout_key(struct_symbol)`) and :791 for the class case use the SAME funnel, documented at module_lowering.spl:161/701 as "the single funnel" with defining_module normalization. The bare name survives only as a lower-priority fallback tier, so the cross-import-boundary namespace mismatch is closed.

## 2026-08-17 CRITICAL-lane re-check: the "DID NOT REPRODUCE" close above is WRONG — STILL OPEN

The preceding section closes this row on the reasoning that producer and
consumer "use the SAME funnel" (`composite_layout_key`). That observation is
true and was never in dispute: **both sides always called it.** The mismatch was
never about which function is called — it is about the *input* that function
receives (`symbol.defining_module`, path-form on one side vs dotted logical name
on the other) and the fact that the funnel performs **no normalization**.
Same-function does not imply same-key.

The funnel says so itself, in the current source, verbatim
(`src/compiler/50.mir/_MirLowering/module_lowering.spl:273-284`):

```
    fn composite_layout_key(symbol: HirSymbol) -> text:
        # DELIBERATELY NOT normalized yet -- see the BLOCKER section of
        # doc/08_tracking/bug/mir_qualified_field_key_namespace_mismatch_2026-08-08.md.
        # Wrapping this in mir_layout_canonical_module_name() is the one-line
        # change that makes resolve_field_index's module-qualified tier
        # actually fire across an import, but on its own it is HARMFUL: ...
        val defining_module = symbol.defining_module ?? ""
```

A close that cites this function as evidence of agreement, while the function's
own comment names this doc and states it is deliberately unfixed, is an
unreviewed close. The normalizer `mir_layout_canonical_module_name` exists but
is applied only in `canonical_mir_type_symbol` (`module_lowering.spl:134` def,
`:306` sole use) — never on the layout-key path.

Divergent inputs still confirmed:
- producer, path form: `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:2493`
  `val mod_name = if self.module_filename != "": Some(self.module_filename)`
  (`types.spl:68` documents `module_filename` as a path);
- consumer, dotted form: same file `:752` `...define(local_name, kind, ..., Some(imported_mod.module_name))`
  (also `:791`, `:811`, `:881`).
- construction still bare-keyed: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:3391`
  `val field_names = self.struct_field_order[struct_name]`.

**Verdict: STILL OPEN**, unchanged in substance since the 2026-08-10 dynamic
confirmation. The one-line normalization at `module_lowering.spl:284` remains
HARMFUL on its own and must land with the `struct_value_syms` /
`lower_struct_construct` re-namespacing (~340 refs across 10+ bare-keyed maps),
for which there is still no oracle short of a Stage 3 bootstrap.

**Evidence basis: SOURCE READING ONLY** — nothing was executed for this
re-check. Also note the `Status re-verified 2026-08-17 by source inspection
(triage shard 02)` stamp at the head of this doc cites no file, no line and no
run; it should not be read as evidence in either direction.

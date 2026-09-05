# Bare field reference inside methods is illegal in every lane, yet ~740 product-code sites use it

- **Filed:** 2026-08-10
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  modules fixed; the wider 62-file family is filed here as systemic follow-up.
- **Severity:** High — this is a *coverage suppression* defect, not a lane defect. Every
  method containing a bare field reference is dead on arrival in all four lanes, and the
  only reason it was not noticed is that none of these methods were ever exercised.
- **Component:** product source (`src/os/**`, `src/compiler/**`, `src/lib/**`) — NOT the
  compiler. All engines agree and all reject.
- **Found by:** conversion of `test/unit/os/riscv_dual_arch_spec.spl` to a real spec
  (`ebb2d787193`), which went 22/22 RED with `semantic: variable 'xlen' not found`.
- **Related:** `doc/08_tracking/bug/riscv_dual_arch_spec_shadows_seven_types_missing_required_fields_2026-08-10.md`
  (recorded the lead; had no bug entry of its own until this one).

## The form under test

```
class Desc:
    xlen: i32

    me bare() -> i32:
        return xlen          # bare — no self./me. prefix

    me qualified() -> i32:
        return self.xlen     # qualified
```

Fixture: `test/fixtures/repro/compiler/bare_field_ref/bare_field_reference_repro.spl`

## Determination: bare field reference is NOT legal Simple

The original hypothesis was that this form is legal and the *test-runner interpreter* has a
resolution gap — which would mean product code runs fine elsewhere while being untestable.
**That hypothesis is false.** No lane accepts it. There is no over-permissive lane, because
there is no permissive lane at all.

### Lane x form table

Binary measured: `bin/release/x86_64-unknown-linux-gnu/simple` (the `bin/simple` symlink
target), size 181524312, mtime **2026-08-10 11:06:25 UTC**. Untouched, read-only use.

| lane | invocation | `self.xlen` (qualified) | `xlen` (bare) |
|---|---|---|---|
| plain interpreter | `bin/simple run F` | PASS `qualified=32` | **FAIL** `error: semantic: variable \`xlen\` not found` |
| forced interpreter | `SIMPLE_EXECUTION_MODE=interpret bin/simple run F` | PASS `qualified=32` | **FAIL** same |
| JIT (default) | `bin/simple run F` | PASS | **FAIL at codegen** `GlobalLoad: unresolved identifier 'xlen' (not a global, function, const-data name, or import)` → JIT bails to interpreter → interpreter also fails |
| JIT strict | `SIMPLE_JIT_STRICT=1 bin/simple run F` | PASS | **FAIL** same, `rc=1` |
| test runner | `bin/simple test <spec>` | PASS | **FAIL** `semantic: variable 'xlen' not found` (22/22 RED) |

Two *independent* compiler subsystems reject the form, which is what makes this conclusive
rather than a single-implementation quirk:

1. **MIR/Cranelift codegen** treats the bare identifier as a global load and finds no such
   global — it never considers the receiver's fields.
2. **The semantic/interpreter resolver** emits `variable not found` — it never falls back
   to enclosing-class fields either.

### Documentary evidence

- `doc/07_guide/language/coding_style.md:278` — the Java/C++ migration table lists
  `this.x` → **`self.x` (implicit self)**. The prescribed spelling is `self.x`, never bare `x`.
- `doc/07_guide/language/coding_style.md:310` and `coding_style.md` "General Syntax Mistakes"
  (`fn foo(self)` → `fn foo()`) make clear that **"implicit self" means `self` is not a
  declared *parameter*** — it does *not* mean field names are injected into method scope.
  This is the distinction the kernel code got wrong.
- `doc/07_guide/quick_reference/syntax_quick_reference.md` documents no bare-field form
  anywhere; every field access in it is qualified.
- `doc/06_spec/system/compiler/modules/parser/lexer_parser_grammar_definitions.md:307-308`,
  `doc/06_spec/shared/control_flow/static_fn_spec.md:75`,
  `doc/06_spec/03_system/feature/usage/impl_blocks_spec.md:62` — all define `fn`/`me` as
  supplying an implicit self **parameter**. None permits omitting `self.` on a field.
- `doc/05_design/language/type_checking/compiler_rfc_ufcs.md:226-233` and
  `doc/05_design/language/misc/ui001_unblock_plan.md:74-85` both spell field reads as
  `self.line` / `self.level`. No design document mentions a bare form.

### Source evidence: the fallback does not exist, and nothing else relies on it

- `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:237` `lower_identifier` — the full
  resolution chain is `None` alias → postcondition binding → `@`-SFFI extern → local lookup
  (`ctx.lookup`, :289) → import alias → named callable → `self.globals` → else. The else
  branch (:342+) handles exactly one self-related case, `name == "self"` inside a static
  method (E1032), then falls to lenient-mode `Global(name)/TypeId::ANY` (:368) or
  `LowerError::UnknownVariable` (:380). **Enclosing-class fields are never consulted** —
  even though `self.current_class_type` is in scope right there.
- `src/compiler_rust/compiler/src/interpreter/expr/literals.rs:361` emits
  `variable \`{}\` not found` (E1001) after trying env, functions, classes and units; its
  "did you mean" candidate set is `env.keys() + functions.keys() + classes.keys()` (:338-342).
  Receiver fields are absent from it.
- Pure-Simple side: no `implicit_self` / `self_field` / field-fallback symbol exists in
  `src/compiler/35.semantics/`, `20.hir/` or `10.frontend/`.
  `src/compiler/20.hir/hir_lowering/expressions.spl` resolves a field only when there is an
  explicit base expression (`field_type_for_base_raw` / `field_type_for_owner_raw`).
- Implicit self exists solely as an implicit *parameter* (`inject_self` in
  `hir/lower/module_lowering/function.rs`; `needs_self` in
  `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl`) — never as an
  implicit field scope. This is the precise distinction the affected sources violate.
- **The compiler's own source never uses the bare form**: ~23,988 `self.<field>` occurrences
  across 1,593 `.spl` files in `src/compiler/`, ~57,999 in `src/lib/`. A bare-field scan of
  `src/compiler/35.semantics/resolve.spl` (`MethodResolver`) returned only false positives
  (constructor keyword args, shadowing locals) and no genuine bare field reads. The form is
  an anomaly, not an idiom.

Note on why permissiveness elsewhere would *not* have proved legality anyway: the repo
already documents that struct instances behave as open dicts, where an unknown-field write
silently creates the field. Acceptance by one engine is therefore not evidence of legality.
In this case the point is moot — nothing accepts it.

### Consequence

Because the form is illegal everywhere, `src/os/kernel/arch/riscv_shared/*.spl` and the
other 61 files below contain **methods that cannot execute in any lane**. They compiled
"fine" only in the sense that nothing ever called them. The moment a real spec imports the
real type and calls the method, it goes RED. This is exactly the silent-coverage-suppression
outcome, arrived at from the opposite direction: the code is not untestable-but-working, it
is broken-and-untested.

## Family sweep — this is systemic, not one module

Sweep script (throwaway, not committed): walks every `.spl` under `src/`, excluding
vendored trees, collects each `class`/`struct`'s declared field names, then scans each
method body for those names appearing as bare identifiers that are not locals, params,
loop binders, keywords, or method/named-arg positions. Triple-quoted docstrings are
excluded (they produced ~45% false positives before filtering).

**740 candidate sites across 62 files.** Manual sampling (14 random findings) put precision
at ~12/14; the residual false positives are pattern bindings (`Ok(gdb):`) and tuple
destructuring (`for line, bp in ...`). Call it **~600-700 genuine sites**.

Top affected files:

| sites | file |
|---|---|
| 52 | `src/os/hosted/hosted_browser_renderer_process.spl` |
| 42 | `src/os/apps/smux/smux_layout.spl` |
| 36 | `src/os/kernel/arch/riscv_shared/backend_test_verify.spl` |
| 35 | `src/compiler/70.backend/backend/vhdl/vhdl_decode_memory.spl` |
| 33 | `src/os/smf/smf_dynlib.spl` |
| 32 | `src/compiler/70.backend/backend/vhdl/vhdl_subprogram_diag.spl` |
| 28 | `src/compiler/70.backend/backend/vhdl/vhdl_subprogram_select.spl` |
| 27 | `src/compiler/10.frontend/domain/schema_contract.spl` |
| 27 | `src/os/hosted/hosted_web_content_session.spl` |
| 25 | `src/os/kernel/arch/riscv_shared/dual_arch_contract.spl` |
| 25 | `src/os/http/http3_frame.spl` |
| 25 | `src/os/http/ws_deflate_auth.spl` |
| 24 | `src/compiler/10.frontend/domain/style_theme.spl` |
| 21 | `src/os/kernel/arch/riscv_shared/fpga_orchestration.spl` |
| 21 | `src/os/http/stun_scram.spl` |

The clustering is diagnostic: `vhdl_*`, `domain/*`, `os/http/*`, `os/hosted/*`, `smux_*`
are precisely the modules with thin or absent spec coverage. Each of these files is a
latent 22/22-RED waiting for someone to write a real spec against it.

## Fix

**Layer: product source, not the compiler.** Adding a field-name fallback to identifier
resolution would be the wrong fix — it would have to be added to *both* the codegen and the
semantic resolver, it would introduce a shadowing hazard between fields and locals, and it
contradicts the documented `self.x` spelling. The compiler is behaving correctly.

Applied here: qualified the bare field references in the three `riscv_shared` modules that
`riscv_dual_arch_spec` imports. The remaining 59 files are tracked by this bug.

## Repro commands

```
bin/simple run  test/fixtures/repro/compiler/bare_field_ref/bare_field_reference_repro.spl
SIMPLE_JIT_STRICT=1 bin/simple run test/fixtures/repro/compiler/bare_field_ref/bare_field_reference_repro.spl
sh scripts/check/check-bare-field-references.shs
```

## Verification

`riscv_dual_arch_spec` moved **22/22 RED → 22/22 GREEN** on both duplicate legs:

```
SPEC FILE VERDICT: test/unit/os/riscv_dual_arch_spec.spl    declared>=22 executed=22 passed=22 failed=0 dropped=0
SPEC FILE VERDICT: test/01_unit/os/riscv_dual_arch_spec.spl declared>=22 executed=22 passed=22 failed=0 dropped=0
```

Fixing it took three passes, each surfacing a distinct spelling of the same defect —
worth recording because a single-pattern sweep would have left siblings:

1. expression position (`return xlen == 32`) — 42 sites across the 3 modules;
2. block-condition position (`if rv32_compile:`) — 8 sites, initially missed because a
   `<name>:` guard meant to skip named arguments also skips block colons;
3. block-condition position in `fpga_orchestration.spl` — 4 more of the same.

`scripts/check/check-bare-field-references.shs` — verdict line last on stdout,
`PASS`/`FAIL`/`ERROR` with exits 0/1/2. It carries a **positive control**: it first runs
the repro fixture and requires the lane to reject the known-bad `Desc.bare()`; if the
control does not fire it reports `ERROR — nothing was checked` rather than PASS, so a
clean kernel result can never come from a dead detector.

Live run: `PASS — 4 checks ran, all green`.

**Negative control, proved live.** Reverting exactly one `self.` (line 13 of
`dual_arch_contract.spl`, `return self.xlen == 32` → `return xlen == 32`) and re-running:

```
SPEC FILE VERDICT: ... executed=22 passed=21 failed=1 dropped=0
semantic: variable `xlen` not found
rc=1
```

The check goes non-zero on that revert and the fix was restored afterwards
(line 13 re-verified as `return self.xlen == 32`).

## Follow-up still open

The 59 other files in the sweep are NOT fixed. Each is a latent RED. They should be
swept module-by-module with a spec written per module, not bulk-rewritten blind — the
three-pass experience above shows a naive single-pattern rewrite leaves siblings behind.

### 2026-08-10 follow-up batch: `src/compiler/10.frontend/domain/domain_hardening.spl`

Fixed 11 genuine bare-field-reference sites (expression position only, all inside
one-line `me foo(): return <expr>` bodies — no block-condition-position sites in this
file) across 4 classes: `DomainHardenEntry`, `HardenReport`, `DomainKindRegistry`,
`DomainRegistryReport`. File uses the `me` convention (no `self.` anywhere in the
file), so fixes use `me.<field>` to match existing style.

No spec exists for this module (`test/**/domain_hardening*` — none found), and
`bin/simple test` on a throwaway spec importing it timed out (>2min, daemon/whole-repo
compile cost, not specific to this fix) even after a `.build/test_daemon_light` reset —
consistent with the known daemon-contention trap. Verified instead via direct
execution: copied the fixed module to a scratch file, appended calls exercising every
touched method through `main()`, and ran `SIMPLE_JIT_STRICT=1 bin/simple run
<scratch>.spl` (binary: `bin/release/x86_64-unknown-linux-gnu/simple`, size
181524312, mtime 2026-08-10 11:06:25 UTC) — `ALL PASS`, `rc=0`. Negative control:
reverted `me.parse_status` back to bare `parse_status` in the scratch copy only and
re-ran — reproduced the exact codegen/semantic failure (`GlobalLoad: unresolved
identifier 'parse_status'` / `semantic: variable \`parse_status\` not found`, `rc=1`),
confirming the oracle actually discriminates. No spec/CI artifact was added for this
module in this pass (out of scope — tracked here as still needed); no deeper defect
(mismatched/nonexistent field) was found in this file, all touched identifiers are
declared fields on their enclosing class.

`scripts/check/check-bare-field-references.shs` is scoped only to
`src/os/kernel/arch/riscv_shared/*.spl` (both by its static-scan glob and its spec
targets) — it does not cover this file or the wider family, and was not extended in
this pass. Re-run for completeness: `PASS — 4 checks ran, all green` (unchanged,
confirms this batch did not regress the riscv_shared fence).

## Secondary defect observed (not the subject of this bug)

`bin/simple run` **exits 0** after printing `error: semantic: variable \`xlen\` not found`
in the default lane. Only `SIMPLE_JIT_STRICT=1` produced `rc=1`. A fatal semantic error
that exits 0 is a fail-open measurement trap of the same family as the ones already
catalogued. Worth its own entry.

## 2026-08-10 full-tree census (verified, bounded)

A whole-`src/` census was run to replace the never-independently-verified "740
sites / 62 files" estimate. **Scope: full coverage, whole tree** — all 14,394
`.spl` files under `src/` were scanned (excluding the six vendored paths named
in the task: `src/compiler_rust/vendor/**`, `src/runtime/vendor/**`,
`src/runtime/miniaudio.h`, `src/runtime/stb_image.h`,
`src/runtime/stb_truetype.h`). No part of `src/` was skipped for size/time
reasons — the whole-tree Python scan completed in ~20s.

**Tool**: `scripts/check/census-bare-field-references.shs` (wraps
`scripts/check/census_bare_field_references_scan.py`, new, read-only,
NOT wired into any pipeline/CI, does not touch or replace
`scripts/check/check-bare-field-references.shs`, which remains scoped only to
`riscv_shared`). Method: for each `class`/`struct`, collect its declared field
names from the block header, then scan every non-`static` method body
(indentation-delimited) for bare occurrences of those names not preceded by
`self.`/`me.`, word-boundary matched.

**Syntactic positions scanned** (per task requirement, enumerated before
scanning): `if <field>` block-condition, `while <field>` block-condition,
`return <field>`/`return <expr with field>`, assignment RHS
(`x = <expr with field>`), and general expression position (method calls,
comparisons, interpolation, arithmetic). All five appear in the emitted TSV's
`syntactic_position` column (`if-cond`, `while-cond`, `return`, `assign-rhs`,
`expr`).

**Positive control (proves the scanner is not silently empty)**: took the
already-fixed `domain_hardening.spl`, reverted `me.parse_status` back to bare
`parse_status` in a scratch copy, and reran the scanner against it in
isolation — it reported exactly 1 candidate site at the reverted line, both
before and after each round of false-positive-filter tightening described
below. The unmodified fixed file, and the two already-checked-clean VHDL
files (`vhdl_cdc_primitives.spl`, `vhdl_device_target.spl`), and the 3 fixed
`riscv_shared` modules, all return **0** hits from the full-tree scan —
consistent with prior fixes, not silently blind.

**Verified totals**: **1,550 candidate sites across 210 files** (after
false-positive filtering described below) — well above the unverified "62
files" and, while below "740 sites" as a raw count, the underlying claim that
740/62 was an undercount is confirmed on the file-count axis (210 vs 62,
3.4x) and plausible on the site axis once precision is taken into account
(see below). 421 rows are `high` confidence (`if-cond`/`while-cond`/`return`
positions), 1,129 are `medium` (`expr`/`assign-rhs`).

**Precision estimate and method**: manual eyeball triage of two independent
random 100-row samples (`shuf` seeded via `/dev/urandom`/fixed streams for
reproducibility) drawn from the full candidate list, reading each site's full
source line in context. Iteratively identified and filtered four dominant
false-positive shapes that a single-pattern grep would have missed: (1)
`self.<f> = <f>` / `me.<f> = <f>` constructor-body idiom, where the bare RHS
is the incoming parameter, not a field read; (2) `key: value` named-argument
position, both the simple `field: field,` form and (3) multi-line docstring
prose using a field name as an ordinary English word (only single-line
`"""..."""` and quoted-string-only lines are filtered; mid-block docstring
continuation lines are NOT filtered — a known residual false-positive
source); (4) inline trailing `#` comments (only whole-line comments are
filtered). After these filters, a fresh 100-row sample showed the visible
false-positive rate down to roughly 1-in-10 to 1-in-7 (consistent with the
task's own 1-in-7 expectation), concentrated almost entirely in the two
residual categories: mid-docstring prose and value-position identifiers
wrapped in another call (e.g. `Some(x)`, `bridge.resume()` where `bridge` may
be a local). **This is a heuristic census, not a compiler** — the TSV's
`confidence` column is the mitigation: treat `medium` rows as needing a
before-fix read of the surrounding block, `high` rows (bare comparisons/
conditions/returns) as the most reliable class.

**Per-cluster breakdown** (top-level dir groups, candidate-site counts):

| cluster | sites |
|---|---:|
| src/compiler_rust/lib | 345 |
| src/lib/gc_async_mut | 281 |
| src/lib/nogc_sync_mut | 189 |
| src/lib/nogc_async_mut | 179 |
| src/compiler/70.backend | 124 |
| src/os/http | 69 |
| src/compiler/10.frontend | 58 |
| src/os/compositor | 54 |
| src/lib/common | 49 |
| src/os/kernel | 46 |
| src/os/smf | 33 |
| src/os/apps | 33 |
| src/app/dashboard | 18 |
| src/os/crypto | 15 |
| src/app/dap | 11 |
| src/os/drivers | 10 |
| (18 smaller clusters) | 36 |

Note: `src/compiler_rust/lib` (725 `.spl` files, a mirrored stdlib tree used
by the Rust-seed build path, distinct from the vendored Rust crates in
`src/compiler_rust/vendor/**`) was in-scope per the task's exclude list — it
is NOT one of the six named exclusions — and is the single largest cluster.
Whether it should be treated as a duplicate of `src/lib/**` for fix-dedup
purposes is a follow-up question, not resolved by this census.

**TSV**: `doc/08_tracking/test/bare_field_reference_sites_2026-08-10.tsv`,
1,550 data rows, columns `file, line, field_name, syntactic_position,
prefix_convention, confidence, class`, sorted by file for cluster-batching.

**Coverage statement**: 100% of `src/**/*.spl` (14,394 files) outside the six
named vendor exclusions was scanned by this heuristic. This is NOT a claim of
100% recall — the false-positive filtering work above implies a symmetric
risk of under-matching in files with unusual formatting (e.g. multi-line
conditions, semicolon-joined statements) that this line-oriented heuristic
does not attempt to handle. No sites were fixed in this pass.

## Reconciliation with the field-aware guard (`4f390bb9379`, 2026-08-10)

A sibling change replaced the regex-based detector with a field-aware
analyzer (embedded AWK in `scripts/check/check-bare-field-references.shs`):
it flags an identifier only when it names a declared field of the enclosing
class, is not a parameter/local of the current method, and is not
`self.`/`me.`-qualified — a strictly stronger check than either this census's
line-heuristic or the original regex proxy. That guard's baseline
(`scripts/check/bare_field_reference_baseline.txt`) records **134 sites /
12 files**, but only over its six named clusters (`riscv_shared`, `domain/`,
`vhdl_*.spl`, `smux_*.spl`, `os/http/**`, `os/hosted/**`) — a scope chosen
from the original 62-file guess, not a whole-tree scan.

This census's 1,550-row TSV lists 210 candidate files; 199 of them (all but
11) fall **outside** that six-cluster scope, so they are the part of the
tree the guard does not yet fence. To check whether that outside area hides
real sites the guard is blind to, the field-aware AWK analyzer (extracted
verbatim from the guard script, not reimplemented) was re-run directly
against those 199 files:

- **Raw result**: 347 `file<TAB>class<TAB>field` triples across 108 files.
- **Positive control**: the same extracted analyzer correctly flags the
  guard's own known-good fixture
  (`test/fixtures/repro/compiler/bare_field_ref/bare_field_reference_repro.spl`,
  `Desc.xlen`), confirming the extraction did not silently break the tool
  before trusting a low/zero count from it.
- **Precision spot-check** (12 triples read in full source context, spanning
  `src/compiler_rust/lib/std/src/physics/**`, `src/os/kernel/arch/riscv64/**`,
  `src/lib/gc_async_mut/**`, `src/lib/nogc_sync_mut/**`,
  `src/compiler/90.tools/perf/trace.spl`, `src/compiler_rust/lib/std/src/sdn/lexer.spl`,
  `src/app/ui.electron/main.spl`): **0 of 12 were genuine bare-field sites.**
  Every one traced to the analyzer's docstring blind spot — it strips `#`
  comments and quoted-string literals but does **not** strip triple-quoted
  `"""..."""` docstring blocks, so a class/method docstring that merely
  *mentions* a field name (`"""ref_count starts at 0 after create()..."""`)
  gets misread as a field-declaration or method-body line. In every checked
  case the actual code already used `self.<field>` correctly at every real
  use site.
- **Conclusion**: this sample gives **no confirmed evidence of real
  bare-field sites outside the guard's six-cluster scope.** The 347/108
  figure is very likely dominated by the same docstring artifact, not a
  larger hidden defect population. This is a negative result, not a null
  one — checked and not found, on a 12-triple sample out of 347.
- **Caveat**: 12 of 347 is a small sample (~3.5%); it rules out "the outside
  area is full of real sites" but does not prove zero. A rigorous close-out
  would either (a) teach the analyzer to strip `"""..."""` blocks and re-run
  the outside-scope pass, or (b) hand-triage a larger stratified sample. Not
  done here — out of scope for a census-only pass.
- **This census's own TSV vs. the baseline**: not directly comparable — the
  TSV's line-level heuristic (which does not distinguish field names from
  same-named locals) and the analyzer's field-aware check disagree by
  construction; the TSV should be read as a superset candidate list requiring
  the same per-site triage demonstrated here, not as an independent
  confirmed count.

**Net effect on scope**: the widely-cited 740/62 estimate is superseded.
Verified counts are now: 134 sites / 12 files fenced and confirmed-real
(guard baseline), plus this census's 1,550-row unfenced candidate superset
(210 files) which — on the one sample checked — does not appear to contain a
large population of additional genuine sites beyond what the guard already
covers, pending the docstring-stripping fix above.

## Docstring blind spot FIXED — analyzer now strips `"""..."""` (2026-08-10)

Option (a) from the section above is done. `doc_filter()` was added to the
embedded AWK analyzer in `scripts/check/check-bare-field-references.shs`. It
runs as the **first** rule on every record, carries its open state across
records so multi-line blocks are stripped, handles a same-line `"""..."""`
pair in place (keeping the surrounding code), and resets per file (`FNR == 1`)
so an unterminated block cannot leak into the next file. The existing `#`
comment and quoted-string stripping in `strip_strings()` is untouched.

Measured before/after (reference binary
`bin/release/x86_64-unknown-linux-gnu/simple`, 181524312 bytes, mtime
2026-08-10 11:06:25 UTC; analyzer extracted verbatim from the guard for the
out-of-scope legs):

| property | before fix | after fix |
|---|---|---|
| guard baseline, 6 clusters / 80 files | 134 triples / 12 files | **134 / 12 — unchanged** |
| out-of-scope re-scan, 199 files | 347 triples / 108 files | **181 triples / 44 files** |
| `riscv_shared/` (fixed cluster) | 0 | 0 |
| `domain_hardening.spl` (fixed) | 0 | 0 |
| `domain_hardening.spl` at `904dc148477^` (pre-fix) | 8 triples / 16 hit-lines | 8 / 16 — unchanged |
| control A (compiler lane rejects fixture) | fires | fires |
| control B (analyzer flags fixture) | fires | fires |

`sh scripts/check/check-bare-field-references.shs --static-only` →
`PASS — 3 checks ran, all green`, exit 0.

**Answer to "are baselined triples docstring artifacts?": no — zero of the
134.** The baseline is byte-identical before and after the fix, so no
regeneration/shrink was needed and the two-way ratchet is undisturbed. The 39
in-scope files that do contain `"""` (notably `vhdl_subprogram_{diag,model,
select}.spl`, 22-24 blocks each) happen to place their docstrings where the
class/method state machine already ignored them.

**Out-of-scope result: 347 → 181, i.e. 166 triples / 64 files were docstring
artifacts, confirming the sibling's 12-triple diagnosis as the dominant
cause.** The remaining 181 are NOT genuine sites either — they are a
**second, distinct false-positive family** in the analyzer's local/param
tracking, which the six fenced clusters do not happen to exercise. Sampling
the 291 residual hit-lines:

- **pattern bindings** (~45): `case Some(parent):`, `Ok(gdb):` — the binder
  introduced by a `case`/`if val` arm is not registered as a local.
- **constructor param shadowing** (~42): `self.min_distance = min_distance`
  — the RHS is the ctor parameter, but the param list spans multiple lines
  and only the single-line `(...)` form is parsed into `params`.
- **named-argument positions** (~40): `worker_id: worker_id,` inside a
  multi-line call — the `nxt != ":"` guard only suppresses the *label*, not
  the value, and the value is again a param.

TODO(2026-08-10) — DONE later the same day; see the final section of this file
for the fixtures, the six eliminated families, and the widened scope. Original
text: teach the analyzer multi-line parameter lists and
`case`/`if val` binder locals, then re-run the 199-file out-of-scope pass. Only
after that is the "are there real sites outside the six clusters" question
genuinely closed; today's answer is "the docstring half is closed, and the
residue is a known analyzer gap, not a defect population". The guard's scope
was deliberately NOT widened in this change, because widening it now would
baseline 181 known-false triples.

## 2026-08-10 (later): all analyzer false-positive families eliminated; scope widened

The TODO above ("teach the analyzer multi-line parameter lists and `case`/`if val`
binder locals, then re-run the 199-file out-of-scope pass") is **resolved**.

Binary measured: `bin/release/x86_64-unknown-linux-gnu/simple` (the `bin/simple`
symlink target), size 181524312, mtime 2026-08-10 11:06:25 UTC; read-only use.
Analyzer claims use `--static-only`, gated on exit code AND the verdict line.

### Fixture-first: every family reproduced before it was fixed

`test/fixtures/repro/compiler/bare_field_ref/bare_field_reference_false_positive_repro.spl`
holds one class per family, plus `GenuineSite.real_field` — a real bare field
reference — as the fixture's own positive control. Before the fix the analyzer
reported **10 false triples + the genuine one**; after, it reports **exactly the
genuine one**. This is now wired into the guard as **control C**, which ERRORs
(exit 2) both when the analyzer reports more than that one triple (an FP family
regressed) and when it reports none (the analyzer went blind).

| # | family | example | fix |
|---|---|---|---|
| 1 | `case`/`if val` binders | `case Some(entry):` | `register_binders()` registers lowercase pattern identifiers as locals; for `if/while val` only the pattern side (before `=`) is scanned, so the RHS stays checked |
| 2 | multi-line parameter lists | `self.min_distance = min_distance` | signature lines are re-joined until parens balance (`paren_balance`), then parsed once (`parse_params`) |
| 3 | named-argument VALUES | `worker_id: worker_id,` | falls out of 1+2; the value is a binder or a multi-line param |
| 4 | pipe/arrow match arms | `\| Some(threshold) ->` | same binder registration, `\|`-form |
| 5 | escaped quotes in literals | `out + ",\"tid\":"` | `strip_strings()` now honours `\` escapes; without it the escaped quote flipped the quote state and the literal body was scanned as code |
| 6 | call targets / kwarg labels | `ticks()`, `device=self.device` | an identifier followed by `(` or `=` is a call target or a label, not a read |

Families 4-6 were **not** in the prior triage — they were found by hand-reading
the residue after families 1-3 were fixed, exactly the "fourth FP family"
question this pass was asked to answer.

### Measured, per property (all re-proven after every change)

| property | before | after |
|---|---|---|
| control A (compiler lane rejects positive fixture) | fires | fires |
| control B (analyzer flags positive fixture) | fires | fires |
| control C (analyzer reports exactly 1 triple on FP fixture) | n/a (new) | holds |
| `riscv_shared/*.spl` | 0 | **0** |
| `domain_hardening.spl` | 0 | **0** |
| `domain_hardening.spl` at `904dc148477^` (pre-fix) | 8 | **8 — detection preserved** |
| in-scope baseline (old 6 clusters) | 134 / 12 files | **130 / 10 files** |
| out-of-scope, 199 census files | 181 / 44 files (296 hit-lines) | **52 / 4 files (79 hit-lines)** |
| guard, widened scope | 134 / 80 files | **182 / 122 files** |

**The in-scope baseline moved, and every entry was investigated.** Seven triples
left (all false) and three arrived (all genuine):

- **-6** `src/os/hosted/hosted_browser_renderer_registry.spl` (5, family 2/3: a
  multi-line `static fn create(...)` whose params feed `window_id: window_id,`)
  and `src/os/hosted/hosted_web_content_session.spl` (1, family 1: `Ok(bookmark_store):`).
  Read in full source context — all six were binder/parameter reads, not field reads.
- **-1** `src/compiler/10.frontend/domain/schema_contract.spl` `identity`, which
  occurs only inside `"\"x-identity\":\"{self.identity}\""` (family 5).
- **+3** `src/os/http/ws_deflate_auth.spl` `DigestResponse.{username,realm,nonce}`
  at line 146, `return "Digest username=\"" + username + ...` — **genuine**, and
  previously MASKED by the escape bug. The escape fix made the guard stronger,
  not weaker.

### Residue hand-verified, then scope widened

All **79** residual hit-lines (not a sample — the whole set) were read in source
context. Every one has the same shape as the original defect: `me is_runtime()
-> bool: return role_name == "runtime"`. There is no fourth FP family left in the
residue. Independently confirmed on the compiler lane, following the guard's own
stderr-marker pattern rather than an exit code:

```
$ bin/simple run <driver calling LibraryRole.runtime(1).is_runtime()>
error: semantic: variable `role_name` not found
```

Because the residue is **all genuine**, the guard's scope was widened to
`src/os/kernel/arch/riscv64/*.spl` (35 files, 31 sites) and `src/os/smf/*.spl`
(7 files, 21 sites) — the only two clusters the residue lives in. Scanning those
whole directories adds exactly the 52 verified triples and nothing else, so no
unverified site was baselined. The file-count floor rose 60 → 100 and the
full-mode check floor 5 → 6 so neither gate got looser as scope grew.

`sh scripts/check/check-bare-field-references.shs --static-only` →
`static OK — 122 files scanned, 182 known site(s), 0 new, 0 stale` /
`PASS — 4 checks ran, all green`, exit 0.

**Remaining work is now product-side, not analyzer-side**: the 182 baselined
sites are real dead methods and still need fixing. The analyzer no longer has a
known false-positive family, so a further scope widening is a scanning decision,
not a precision one.

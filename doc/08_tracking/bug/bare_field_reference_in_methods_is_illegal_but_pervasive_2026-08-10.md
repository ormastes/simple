# Bare field reference inside methods is illegal in every lane, yet ~740 product-code sites use it

- **Filed:** 2026-08-10
- **Status:** Root-caused. Determination settled: the form is ILLEGAL. Kernel `riscv_shared`
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

## Secondary defect observed (not the subject of this bug)

`bin/simple run` **exits 0** after printing `error: semantic: variable \`xlen\` not found`
in the default lane. Only `SIMPLE_JIT_STRICT=1` produced `rc=1`. A fatal semantic error
that exits 0 is a fail-open measurement trap of the same family as the ones already
catalogued. Worth its own entry.

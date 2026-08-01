# lenient_types turns any unresolved name into a global with no diagnostic

- **Date:** 2026-08-01
- **Component:** `src/compiler_rust/compiler/src/hir/lower` (Rust seed HIR lowering)
- **Severity:** systemic diagnostic failure (not a miscompile)
- **Status:** attribution landed; the leniency itself is retained by design

## Symptom

An ordinary typo, or an HIR scope bug, produces **no diagnostic at all** during
compilation and instead fails at **link** time as a bare undefined-symbol name,
thousands of lines from the source, with no file, no line and no function.

## Mechanism (PROVED)

`hir/lower/expr/mod.rs` — under `lenient_types`, a name that resolves to no
local, no callable and no global becomes:

```
HirExprKind::Global(name)  ->  MirInst::GlobalLoad  ->  undeclared LLVM symbol
```

`mir/lower/lowering_expr_ident.rs` emits the `GlobalLoad` keyed by name;
`codegen/instr/mod.rs` and `codegen/llvm/backend_core.rs` resolve that name
against `global_ids`, then `func_ids`, then `use_map` / `import_map` with
`Linkage::Import`. If nothing defines it, the failure is deferred to the linker.

Proved by `undefined_identifier_is_lowered_as_a_global_under_lenient_types`:
lenient lowering of `fn probe() -> i64: return totally_undefined_name`
**succeeds** and the undefined name is present as a `Global`.

Note the strict path is fine — `simple compile --native` on a single file
reports `error: semantic: Undefined("undefined identifier: X")`. The lenient
`native-build` / `native_project` lane is where the signal is lost. This was
already documented at `pipeline/native_project/compiler.rs:130-142`: *"under
`native-build` there is no error at all and the sibling reads an uninitialized
global, which is strictly worse."*

## Two instances that cost significant effort

- `interp_list` — a compiler bug, not a typo. `Expr::If` carries a
  `let_pattern` field that the HIR dispatcher matched with `..` and dropped, so
  `lower_if` never registered the bound name. Fixed in `a1c93dd7167`. The
  interpreter had the identical defect, fixed 2026-07-20; the LLVM/JIT sibling
  was left behind. Instance doc:
  `if_val_expression_binding_lost_hir_2026-08-01.md`.
- `animation_time_ms` — a plain undefined identifier in
  `_simple_web_layout_compose_retained` (21 params, none named that). Instance
  doc: `web_renderer_compose_retained_missing_animation_time_param_2026-08-01.md`.

## Why the leniency was NOT removed (INFERRED from code, PROVED for the
resolution gap)

The fallback is **load-bearing**. `native_project::lower_file` lowers one file
at a time, and `self.globals` is populated only from the current AST module's
own items (`module_lowering/module_pass.rs`); nothing repopulates it afterwards.
A reference to a function, const or enum variant defined in a **sibling file**
is therefore necessarily unresolvable at HIR time and must survive as a `Global`
so codegen can bind it via `use_map` / `import_map`. Making this an error would
break all cross-module compilation.

Enable sites and their stated reasons:

| Site | Reason |
|---|---|
| `hir/lower/mod.rs` (`lower_lenient`) | "bootstrap compilation and backwards compatibility" |
| `pipeline/execution.rs` | gated on `bootstrap_mode`; mirrors the native_project flow |
| `pipeline/native_project/compiler.rs` (`lower_file`) | per-file lowering; cross-module resolution gap |
| `driver/exec_core.rs` | copies lenient mode to align W1006 strictness across lanes |

Git history cannot corroborate the original motivation: `git log -S
"lenient_types"` returns only tree-restore / conflict-repair / hourly-sync
commits, so the introducing commit was squashed away by a VCS incident.

## Fix: attribute, do not reject

`hir/lower/lenient_global_diag.rs` records every name the lenient fallback
lowers to a global, with the file, the enclosing function and that function's
declaration line. `Expr::Identifier(String)` carries no span, so the enclosing
function's line is the tightest attribution available without an AST change —
enough to locate the name.

Compilation behaviour is unchanged. The record is surfaced on
`LoweringOutput.lenient_globals`, with `attributions_for(symbol)` as the
link-failure entry point: given "undefined symbol X" from the linker, it returns
the source locations that emitted it.

All four lenient fallbacks that mint a symbol name are instrumented (the family,
not just the reported member): unresolved identifier, unresolved `@` SFFI
extern, `Type.new` as global, and dotted path.

Per-name printing is level-gated and **default off** (the population is
dominated by legitimate cross-module names, so always-on would be noise):

```
SIMPLE_DIAG_LENIENT_GLOBALS=1
```

## Population census (measured 2026-08-01, base `5ca84bcefe5`)

`compiler/tests/lenient_global_census.rs` (ignored by default):

```
cargo test -p simple-compiler --test lenient_global_census -- --ignored --nocapture
```

Over `src/compiler`, `src/lib`, `src/app`:

| Metric | Count |
|---|---|
| files scanned | 11,380 |
| parsed ok | 11,335 |
| parse failed | 45 |
| lowering failed | 983 |
| distinct names attributed | 2,094 |
| **of those, undefined tree-wide** | **580** |

The 580 are attributed names for which no file in the scanned set defines a
matching function, class, struct, enum, enum variant, extern, type alias, actor
or module-level `val`/`const`/`static`. They cannot be satisfied by any sibling
module, so they are the queue of future link blockers. Rough shape (measured on
the 584-name run below): ~488 lower_snake (function/variable class), ~20
CamelCase, ~14 UPPER_SNAKE.

**580 is a lower bound** — the 983 files that failed lenient lowering and the 45
that failed parsing contribute nothing to the count.

### Validation: the count responds to a real fix (PROVED)

Run twice, on two trees differing only by the landed `interp_list` fix:

| Tree | attributed | undefined tree-wide | `interp_list` present? |
|---|---|---|---|
| `ca8ff9e003d` (predates the fix) | 2,101 | 584 | **yes** |
| `5ca84bcefe5` (fix landed) | 2,094 | 580 | **no** |

On the pre-fix tree the census independently surfaced the known blocker at
`src/compiler/20.hir/hir_lowering/module_surface.spl:240 in
module_surface_from_module` — a live defect located by source line instead of by
link error, which is exactly the intended outcome. On the post-fix tree it is
gone. The metric tracks real defects rather than counting noise.

`animation_time_ms` is **not** present at either commit (the reference in
`simple_web_html_layout_renderer.spl` is a declared parameter here), so that
instance is covered by a shape-equivalent regression test rather than a live
census hit.


## Verification

- `cargo test -p simple-compiler --lib lenient_global_diag` — 10 passed.
- Full `cargo test -p simple-compiler --lib`: 3,443 passed / 115 failed, vs
  baseline 3,433 passed / 115 failed. The 115 failing test **names are
  set-identical** before and after (compared by `comm`); the delta is exactly
  the 10 new tests. No regressions.

## Follow-ups (not done here)

- `Expr::Identifier` has no span, so attribution is function-granular. Giving
  identifiers a span would make it line-exact.
- Nothing yet consults `attributions_for` automatically when the linker reports
  an undefined symbol; wiring that into the native-link error path would close
  the loop end to end.
- The 580 undefined names are unreviewed. Each is either a real defect or a
  name resolved by a mechanism the census does not model.

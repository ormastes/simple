# BUG: seed interpreter poisons cross-module struct field access to `Option` under a broad import closure

- **ID:** `seed_crossmodule_struct_field_option_poison`
- **Severity:** P1 (false-RED on a green GUI gate; blocks any `run --mode=interpreter` app that
  imports the engine2d CPU backend + the widget builder + draw-cmd projector together)
- **Found:** 2026-06-14, `check-responsive-showcase-evidence` CPU + Metal lanes.
- **Regression window:** present in `src/compiler_rust/target/release/simple` (built 2026-06-13
  14:57); NOT present in deployed `bin/release/aarch64-apple-darwin-macho/simple` (2026-06-06).
  So it landed in the Rust seed between 2026-06-06 and 2026-06-13. Memory records the gate shipping
  green on 2026-06-13, consistent with a same-day seed regression.
- **Related:** [[project_mobile_gui_platform_2026-06-13]] (the gate this breaks);
  cross-module return-type / import-map notes in MEMORY.md.

## Symptom
Running either responsive-showcase app under the dev seed interpreter:

```
SIMPLE_LIB=src src/compiler_rust/target/release/simple run \
  examples/06_io/ui/responsive_showcase_gui.spl --mode=interpreter
→ error: semantic: undefined field: unknown property or method 'kind' on Option
```

`cmd` iterates a `[DrawCmd]` (return of `widget_tree_to_draw_cmds`, declared `-> [DrawCmd]`).
`DrawCmd` is a plain struct with a `kind: text` field. The compiler types the loop element as
`Option` instead of `DrawCmd`, so `cmd.kind` is rejected. Deterministic (10/10 runs).

## Minimal repro (verified)
The irreducible trigger is the **combination** of three imports — drop any one and it compiles:

```simple
use std.gpu.engine2d.backend_cpu.{CpuBackend}
use common.ui.builder.{column, label}
use common.ui.widget_draw_cmds.{DrawCmd, widget_tree_to_draw_cmds}

fn main():
    val root = column("r", [label("a", "hi")])
    val cmds: [DrawCmd] = widget_tree_to_draw_cmds(root, 100, 100)
    for cmd in cmds:
        if cmd.kind == "rect":   # → "unknown property 'kind' on Option"
            print "RECT_OK"
```

- `backend_cpu` is the heavy ingredient: `builder + widget_draw_cmds` alone is fine; adding
  `backend_cpu` (large transitive closure) poisons it.
- NOT specific to `ppm_decode` / `Result` returns: a trivial third module exporting one
  `-> [u8]` fn triggers it just as well once `backend_cpu` is imported. Points at an import-map
  symbol collision / capacity issue, not return-type inference of any single function.

## Refined root cause (2026-06-14, post-rebuild) — RUNTIME marshalling, not static inference
- Statically `cmd` IS correctly typed `DrawCmd`: HIR lowering rejects `cmd.is_some` with
  "cannot infer field type … struct 'DrawCmd' field 'is_some'". The type checker knows it's a DrawCmd.
- At **runtime** the interpreter holds `cmd` as `Value::Enum{ enum_name:"Option" }` → `.kind` hits
  `interpreter/expr/calls.rs:779` ("unknown property … on Option").
- So `widget_tree_to_draw_cmds` (declared `-> [DrawCmd]`) returns an array whose **elements are
  Option-wrapped** crossing the module boundary back to the caller — only with `backend_cpu`'s large
  closure also in the unit. The marshalling site is not grep-localizable; needs bisect/instrumentation.
- Same family as OPEN bug `interp_run_cross_module_db_option_mutation` (2026-06-13): cross-module
  Option/struct returns mis-marshalled in the interpreter `run` path.
- Survives all 131 commits landed 06-13..06-14 incl fix(seed) a60b5453 / fix(hir) 17991574
  (fresh `cargo build --release -p simple-driver` still reproduces, 3/3).

## Workarounds tested — ALL FAIL
The corruption is global to type resolution, not local inference, so use-site annotations do not help:
- `val cmds: [DrawCmd] = ...` — still poisoned.
- `for cmd: DrawCmd in cmds` — parse error (syntax not supported).
- inner rebind `val cmd: DrawCmd = raw` inside the loop — still poisoned.
- passing `cmds` to a helper with an explicit `cmds: [DrawCmd]` parameter — still poisoned.

There is no app-level escape: `backend_cpu` (render), `builder` (build tree) and
`widget_draw_cmds` (project) are all essential to these apps.

## Impact
- `check-responsive-showcase-evidence` is RED **only** because it prefers
  `src/compiler_rust/target/release/simple` over `bin/simple`. With `SIMPLE_BIN=bin/simple` the gate
  is fully GREEN: CPU nav_patterns bottom/rail/sidebar, PPMs pairwise-different, Metal
  `gpu_frame_complete=true × 4`. The GUI/2D apps and libs are correct.

## Proposed next step (staged — NOT done here; seed change needs full bootstrap verification)
1. Confirm in the current seed source (`cargo build --release -p simple-driver`) that the dev binary
   still reproduces — i.e. the regression is in current `main`, not a stale artifact.
2. Locate the import-map / cross-module symbol table build in `src/compiler_rust` (semantic
   analyzer) where a large closure remaps a struct's field-bearing type to `Option`. Likely a
   collision in the `raw_to_mangled` / `build_import_map` merge (see MEMORY.md cross-module notes).
3. Add the 3-import repro as a regression fixture once fixed.

## GUI path FIXED; Option representation split partially healed (2026-06-15, commits e9ee640c + field-forward follow-up)
The "import-map / type-inference" framing above was a red herring — it is a **runtime value
marshalling** bug. Culprit: `60fd804c` ("auto-wrap plain returns into Option for `-> T?`",
2026-06-12) made `-> T?` functions return explicit `Option::Some(x)`, but the rest of the
interpreter still represents Optionals as `plain value | nil`. So a Some-wrapped value funneled into
a non-Optional sink stayed wrapped, and member access on it failed with "… on Option". The
responsive-showcase path hit it via `require_widget_record() -> WidgetRecord` (returns `found` from
a `-> WidgetRecord?` call) and the `[WidgetNode]` children pipeline.

Fix — conservative `Some`-coercions at four sinks (each gated on `Value::Enum{Option,Some}`; the
return/param/field cases additionally require a *concrete* non-Optional type — `any`/`Option`/
`Result`/bare-generics excluded). `None` is never unwrapped, so nil-dereferences still error:
- `interpreter_call/core/function_exec.rs` — unwrap `Some(x)→x` on a concrete non-Optional **return** (e9ee640c).
- `interpreter_call/core/arg_binding.rs` — same unwrap binding into a concrete non-Optional **param** (e9ee640c).
- `interpreter_method/mod.rs` — forward a user **method call** on `Some(x)` to the inner value, only
  after every real Option/Result/enum method has missed (e9ee640c).
- `interpreter/expr/calls.rs` — **field access** on `Some(Object)` reads the field off the inner
  struct (field-forward follow-up). Without this, `Some(struct).field` still hit "… on Option" on
  any path the upstream coercions didn't pre-unwrap.

**This is a PARTIAL heal, not a full fix of 60fd804c's representation split.** Other sinks remain
unpatched — `match` expressions, `==`, and direct use of a bound Optional (e.g.
`val a = find(); print "{a}"` prints `Option::Some(10)`, not `10`). Recurrence is possible if new
code routes a `Some` into one of those. The proper long-term fix is to make the whole interpreter
agree on ONE Option representation. Known caveat: the method-call Some-forwarding re-dispatches via a
temp receiver, which re-evaluates the call's args; for a method that misses every Option/Result/enum
handler AND has effectful args, those args evaluate twice (the GUI path has no such call).

Verification: responsive-showcase gate GREEN on the freshly-built dev seed (CPU nav bottom/rail/
sidebar, PPMs pairwise-different, Metal `gpu_frame_complete=true × 4`); `Some(struct).field` and
`Some(struct).method()` both work, `None.field`/`None.method()` still error (nil-safety). All
function-exec / arg-binding / method-dispatch unit tests in `simple-compiler` pass (364 interpreter
tests; the 190 crate-wide failures are pre-existing, in `value::matches_type`, runtime-archive
selection and module path-resolution — subsystems this change never touches). NOTE: a full 3-stage
bootstrap was NOT run (interpreter-only change; disk-constrained env) — run `bin/simple build
bootstrap` to fully certify.

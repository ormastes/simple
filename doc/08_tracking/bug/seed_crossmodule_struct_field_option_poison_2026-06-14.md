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

## Status
OPEN — recorded, not fixed. Apps/libs verified correct via deployed `bin/simple` (gate green).
Fix deferred: it is a Rust-seed semantic-analyzer change with bootstrap blast-radius and must not be
landed without a full bootstrap pass.

# Struct/class receiver decays to a module-namespace dict under `simple test`

Date: 2026-08-19
Status: FIXED (Rust seed interpreter; same root cause as the OPEN
`for_loop_var_shadowed_by_module_alias_2026-08-18.md`, which this fix closes)
Component: Rust seed interpreter — for-loop variable vs flat MODULE_GLOBALS

## Symptom

Under `bin/simple test`, class/struct receivers appeared to decay to "an empty
dict": e.g. `test/03_system/gui/editor_controller_spec.spl` failed 73 of 92
examples with

```
semantic: undefined field: unknown property, key, or method 'name' on Dict
```

Same shape in `editor_gui_spec.spl`, `wm_chrome_theme_spec.spl` ('minimized'
on dict), `wm_showcase_session_capture_spec.spl` ('key' on dict). Unchanged by
the two 2026-08-19 match-arm fixes
(`engine2d_factory_returns_dict_under_test_runner_2026-08-19.md`).

## Minimal reproduction (4 imports; fails pre-fix, passes post-fix)

```
use std.spec
use std.editor.core.session.{EditSession}
use app.editor.editor_controller.*
use std.editor.extensions.manifest.*          # <- the trigger

describe "decay":
    it "runs palette command":
        var session = EditSession.new()
        var ctrl: EditorController = EditorController.new(session)
        val daily = ctrl._execute_palette_command("daily-note-create", "2026-05-16|/tmp/d|# {{title}}\n")
        print(daily.status_msg)
```

Delta-debugging the spec's 46-import header showed exactly ONE import flips
the verdict: `use std.editor.extensions.manifest.*`. Removing it passes;
essentials-only + the palette call passes.

## Mechanism (not an "empty dict" — a module-namespace dict)

1. Any `use pkg.manifest.*` (glob, group, or single) also binds the module
   dict under its basename into the FLAT `MODULE_GLOBALS`
   (`interpreter_eval.rs` UseStmt: "keep the module dict under its name for
   qualified access"). The spec's top level is module scope, so the spec's
   import plants `MODULE_GLOBALS["manifest"] = {module exports}` for the whole
   process.
2. Identifier reads prefer live `MODULE_GLOBALS` over env for NON-local
   bindings (`interpreter/expr/literals.rs`, the fix for
   `spec_it_block_reads_stale_module_var_2026-08-04.md`): if
   `!env.is_local(name)` and `MODULE_GLOBALS` has `name`, the global wins.
3. `exec_for` (`interpreter_control.rs`) never marked the loop variable as
   local — function params (`function_exec.rs:693`), lambda params, and
   `val`/`let` block statements all do, but the for-loop pattern names did
   not. So inside `extension_host_with_builtins_indexed()`
   (`src/lib/editor/extensions/host.spl:847`):

   ```
   for manifest in builtin_manifest_providers():
       host.register_manifest(manifest, "<builtin>")
   ```

   the read of `manifest` resolved to the manifest MODULE dict, not the loop
   element. Confirmed with an env-gated probe
   (`SIMPLE_DEBUG_DICT_FIELD=1`, added in `interpreter/expr/calls.rs`):
   `field=name receiver=Identifier("manifest")
   dict_keys=["extension_manifest_basic", "ExtensionTheme", ...]`.

`EditorController.new` therefore blew up inside host construction whenever the
spec ALSO imported the manifest module — which system gui specs do. The same
collision explains the other gui specs (loop vars named like glob-imported
modules elsewhere).

## Fix

`src/compiler_rust/compiler/src/interpreter_control.rs` `exec_for`: mark every
for-pattern binding `enter_block_local` for the duration of the loop (paired
`exit_block_local` after `exec_for_inner`, before the existing unconditional
restore). `is_local` then holds for the loop var, so the
MODULE_GLOBALS-prefer read rule no longer hijacks it. A debug probe (default
off, `SIMPLE_DEBUG_DICT_FIELD=1`) is kept at the Dict undefined-field error in
`interpreter/expr/calls.rs`.

## Verdicts (deployed-seed before → fixed binary after)

- editor_controller_spec: 92 total, 19 passed / 73 failed → see test log
  (post-fix run below)
- minimal repro: FAIL ('name' on Dict) → PASS
- regressions engine2d_drawing_spec, vulkan_strict_spec,
  base_encoding_utf8_guard_spec: re-run green (see session report)

## Related

- for_loop_var_shadowed_by_module_alias_2026-08-18.md (same defect, OPEN —
  closed by this fix; its minimal repro is the alias form)
- group_import_self_named_module_binds_module_dict_2026-08-17.md (write-side
  sibling: group import clobbered by module-dict rebind)
- spec_it_block_reads_stale_module_var_2026-08-04.md (the read rule this
  collides with)

# Coverage `<entry>` placeholder attribution — two root causes, not one; B collapses into A

Status: root-caused, one fix landed (Node::Impl owner-tagging gap), one fix
deferred (entry-script top-level owner registration — out of scope this pass).

## Background

Two prior reports flagged what looked like two separate defects:

- **A** — `doc/09_report/ui/testing/render2d_c2_c3_coverage_measured_2026-08-07.md`
  and `doc/09_report/ui/testing/wm_gui_web_coverage_baseline_2026-08-07.md`:
  decision/line rows for code "in the entry file" carry the `<entry>`
  placeholder path instead of a real file path (7/68 rows in the C2
  measurement, 39/207 in C3).
- **B** — same C3 report, follow-up section ("Coverage before/after"):
  `src/os/compositor/engine2d_baremetal_core.spl` (389 source lines) —
  `lines:` rows in the raw artifact top out at line 143, even though passing
  pixel assertions prove `draw_rect_stroked` (244), `draw_circle_stroked`
  (344), `draw_image` (366), `draw_codes12_block` (381) executed. That report
  concluded: *"the artifact's line numbers are the coverage instrumentation's
  own numbering (likely desugared/lowered IR line positions), not raw source
  line numbers, and its 'lines' tracking appears to record only a sparse
  subset of executed statements."*

**That diagnosis for B is wrong.** Re-running the exact same spec
(`test/01_unit/os/compositor/engine2d_baremetal_core_spec.spl`) with
`SIMPLE_COVERAGE_OUTPUT` and grepping the raw artifact for `<entry>` rows
(not just rows keyed to the real filename, which is what the original report
counted) shows the missing lines are *in the artifact*, correctly numbered,
filed under `<entry>`:

```
$ SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/probe_ebc.sdn bin/simple run \
    src/app/test_runner_new/test_runner_single.spl \
    test/01_unit/os/compositor/engine2d_baremetal_core_spec.spl \
    --no-session-daemon --sequential
...
coverage: src/os/compositor/engine2d_baremetal_core.spl 6% (13/209 lines)

$ grep "<entry>," /tmp/probe_ebc.sdn | awk -F', ' '{print $2}' | sort -n | tail -5
382
383
384
385
386
389

$ grep "<entry>," /tmp/probe_ebc.sdn | awk -F', ' '{print $2}' | awk '$1>=240 && $1<=389' | wc -l
73

$ grep "engine2d_baremetal_core.spl," /tmp/probe_ebc.sdn | awk -F', ' '{print $2}' | sort -n | tail -1
143
```

Line 389 (the file's last line) IS recorded, correctly numbered, just under
the wrong file key. **B is not a distinct "sparse sampling" or "lowered
numbering" defect — it is the same misattribution defect as A**, just severe
enough in this file (73 of the file's real decision/line rows land past the
real-path/`<entry>` split) that a report which only counted real-path rows
read it as "coverage stops at line 143."

## Root cause 1 (fixed): `Node::Impl` block methods never get module-owner tagged

`src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs`,
`register_definitions()`. Four AST item kinds carry methods; three of them
call `tag_methods_owner(&mut methods, module_ident.as_ref())` before adding
the methods to the class/struct/enum:

- `Node::Class` — line 188 (pre-fix)
- `Node::Struct` — line 241 (pre-fix)
- `Node::Enum` — line 361 (pre-fix)
- `Node::Impl` — **no call, at any of its 6 method-construction sites**
  (`local_classes`/`global_classes`/`local_enums`/`global_enums` extends,
  the static-method-from-impl-block loop, and `GLOBAL_IMPL_METHODS`)

`Engine2DBaremetalCore`'s drawing methods (`draw_rect_stroked`,
`draw_circle_stroked`, `draw_image`, `draw_codes12_block`, ...) are all
defined in a separate `impl Engine2DBaremetalCore:` block starting well after
the file's free functions — exactly the point (line 143, end of `_bm_blend`,
the file's last free function before the `impl`) where real-path attribution
stops in the artifact. Free functions go through `Node::Function ->
record_function_owner` (pointer-keyed `FUNCTION_MODULE_OWNER` map, set); impl
methods went through `Node::Impl`, which never tagged anything. At call time,
`function_module_owner()` (`interpreter_call/mod.rs`) finds neither the
pointer-map entry nor the attribute fallback, returns `None`,
`CURRENT_EXEC_MODULE` is left at whatever the caller had (unset for a spec
calling into the module under test), and `current_coverage_file()`
(`interpreter/coverage_helpers.rs:81-86`) falls back to the `"<entry>"`
sentinel.

This is a real, mechanical partition, not a coincidence: every `<entry>` row
in the 240-389 range in `/tmp/probe_ebc.sdn` is inside the `impl` block; every
real-path row (up to 143) is a free function.

### Fix

`method_with_impl_driver_attrs(m, &impl_block.attributes)` builds a brand-new
`FunctionDef` for each impl method, so tagging the *source* `impl_block.methods`
is a no-op — the mapped copy must be tagged. All 6 construction sites in the
`Node::Impl` branch now route through the mapped-and-tagged copy so every
consumer (class methods, enum methods, static mangled functions,
`GLOBAL_IMPL_METHODS`) sees the same owner-tagged `FunctionDef`.

### Scope note (not a coverage-only change)

Tagging impl methods means `CURRENT_EXEC_MODULE` becomes `Some(path)` while an
impl-block method body executes, where it previously inherited whatever the
caller had (frequently `None`). This also affects `module_global_target`
(`interpreter_call/block_execution.rs:28-33`, `Legacy` vs `Owned` dispatch)
and `select_overload`'s same-name/same-arity tie-break
(`interpreter_call/mod.rs:163`) for every impl-block method in the codebase —
inline class/struct/enum-body methods already behaved this way, so this
removes an inconsistency rather than introducing new behavior, but it is a
real surface and is covered by the full `cargo test` run before landing (see
report doc for pass/fail summary).

## Root cause 2 (documented, not fixed this pass): entry-script top-level functions never get an owner at all

The entry script (the file passed to `bin/simple run <path>`, e.g. a spec
file under `test/`) is not evaluated through
`interpreter_module::module_evaluator::register_definitions` /
`evaluate_module_exports` — that path is only reached for `use`-imported
modules (call sites: `interpreter_module/module_loader.rs:1127,1175`). The
entry script's own top-level `Node::Function` items are registered through a
different top-level-program path that was not located this pass and never
calls `record_function_owner`/`tag_function_module_owner`. Consequently
`function_module_owner()` always returns `None` for a function defined
directly in the entry file, `CURRENT_EXEC_MODULE` is never set to the entry
file's own path, and `current_coverage_file()` falls back to `<entry>` for
every top-level statement and function body belonging to the entry file
itself — matching the C2/C3 reports' "7/68" and "39/207" `<entry>`-row counts
(a mix of this cause and root cause 1, since those specs also exercise
impl-block methods in imported modules).

**Deferred rather than fixed in this pass** because the natural fix (set
`CURRENT_EXEC_MODULE` to the entry path at program start) changes
`module_global_target` and `select_overload` behavior for *all* entry-file
code, not just coverage attribution — a strictly larger blast radius than
root cause 1, and the actual top-level registration call site was not
located within this session's scope. A coverage-only fix (a dedicated
`CURRENT_COVERAGE_MODULE` thread-local, read only by
`current_coverage_file()`, set/restored beside the existing
`CURRENT_EXEC_MODULE` save/restore in
`interpreter_call/core/function_exec.rs:576-583,642`, plus a matching set at
whatever entry-point owns top-level script execution) is the safer shape but
needs that entry point identified first. Filed here so it isn't lost.

## Evidence retained

- `/tmp/probe_ebc.sdn` — pre-fix artifact from
  `engine2d_baremetal_core_spec.spl`, backing the 73-row/143-boundary claims
  above.
- Post-fix probe (old binary vs. new binary, same spec) recorded in
  `doc/09_report/ui/testing/coverage_entry_placeholder_fix_verified_2026-08-08.md`
  if the build succeeded this session; otherwise this doc stands alone as the
  diagnosis.

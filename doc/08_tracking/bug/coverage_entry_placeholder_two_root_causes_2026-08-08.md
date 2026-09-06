# Coverage `<entry>` placeholder attribution — two root causes, not one; B collapses into A

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).
the import-module path; entry-script `<entry>`-sentinel coverage fallback;
Node::Impl owner-tagging gap in the sibling script-eval path).

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

## Root cause 2 (fixed 2026-08-08): entry-script top-level functions are tagged with the literal `"<entry>"` sentinel, not a real path

**Correction to the original diagnosis below:** the registration site is not
missing — it was mislocated. The entry script's own top-level `Node::Function`
items ARE registered, in `evaluate_module_impl()`
(`src/compiler_rust/compiler/src/interpreter_eval.rs`, the `Node::Function`
arm, ~line 505 pre-fix). This is the single registration pass
`bin/simple run`/`-c` actually exercises for the root script (imports are
already flattened into `items` by then). It reads back a
`FLATTEN_MODULE_OWNER_ATTR_PREFIX` attribute for functions that were flattened
in from an imported module, and **falls back to the literal string
`Arc::from("<entry>")`** — not `None` — for functions genuinely defined in the
entry script itself, inserting that into `FUNCTION_MODULE_OWNER`. This is
deliberate: it keeps entry-script functions in a distinct tie-break bucket
from any imported module's same-named functions for `module_global_target`
and `select_overload`. So `function_module_owner()` does NOT return `None` for
an entry-script function — it returns `Some("<entry>")`, and calling such a
function sets `CURRENT_EXEC_MODULE` to `Some("<entry>")` via the existing
save/restore in `execute_function_body`
(`interpreter_call/core/function_exec.rs:576-583,642`). `current_coverage_file()`
then returns that literal string verbatim — the `<entry>` sentinel was always
reaching coverage through the "owner is known" path, not the "owner is
`None`" path the original diagnosis (immediately below) assumed.

Entry-script top-level *statements* (module body code outside any function)
are the other, `None`, case: they execute before any `execute_function_body`
call, so `CURRENT_EXEC_MODULE` is genuinely never set for them.

Both cases are matched by the C2/C3 reports' "7/68" and "39/207" `<entry>`-row
counts (mixed with root cause 1, since those specs also exercise impl-block
methods in imported modules).

### Fix

Coverage-only, in `current_coverage_file()`
(`src/compiler_rust/compiler/src/interpreter/coverage_helpers.rs`): when
`CURRENT_EXEC_MODULE` is `None` **or** equals the literal `"<entry>"` string,
fall back to `CURRENT_FILE` — a thread-local the driver already sets to the
entry file's own real path around `evaluate_module`
(`run_file_interpreted_with_args`, `driver/src/exec_core.rs`) and clears
after — normalized through the same `normalize_path_key` used for every other
real-path owner string, so the format matches. Falls through to the `"<entry>"`
string only when `CURRENT_FILE` is also unset (in-memory `-c` source with no
backing file).

This does not write `CURRENT_EXEC_MODULE` or `FUNCTION_MODULE_OWNER` at all —
it only reads them, downstream, for display. `module_global_target`'s
Legacy/Owned dispatch and `select_overload`'s same-name tie-break both key off
the literal `"<entry>"` string in `CURRENT_EXEC_MODULE` directly, not off
`current_coverage_file()`'s return value, so both are byte-for-byte
unaffected — this was the deferred fix's "safer shape," located and landed.

### Verification

A/B probe (`/tmp/cov_probe_rc2/tiny_spec.spl`, a spec with a module-level
`compute()` function containing an `if`, run through
`src/app/test_runner_new/test_runner_single.spl --no-session-daemon
--sequential` under `SIMPLE_COVERAGE=1`):

- OLD (deployed `bin/simple`, itself currently the Rust seed per the Stage-3
  self-host blocker): every `lines`/`decisions` row keyed `<entry>`.
- NEW (`src/compiler_rust/target/release/simple`, this fix): every row keyed
  to the real temp-file path — zero `<entry>` rows.

Regression: `cargo test --release -p simple-compiler --lib coverage` — 513
passed, 53 failed, all 53 in `mir::lower::tests::branch_coverage` (pre-existing,
unrelated to owner-tagging). `cargo test --release -p simple-compiler --lib
overload` — 1 passed, 0 failed (same as RC1 landing). `... --lib entry` shows
5 failures, but they are `pipeline::native_project::tests::*` cases guarded by
a shared `runtime_bundle_env_lock()` mutex unrelated to coverage/interpreter
owner tagging — one test in that family panics (pre-existing, matches the
"one native_project test" noted in the RC1 landing) and poisons the mutex for
the rest of that lock's tests; reproduces identically with `--test-threads=1`,
so it is not new flakiness introduced by this change.

## RC1 sibling (fixed 2026-08-08): the script-eval `Node::Impl` path had the same untagged pattern

Higher-model review of the RC1 landing (`b6a43042`) found a second, parallel
copy of the pre-fix bug: RC1's fix only touched
`interpreter_module/module_evaluator/evaluation_helpers.rs`'s
`register_definitions()` — the path used when a module is loaded as an
*import*. `bin/simple run <file>`/`-c` on the *entry script itself* does not
go through that function at all; its top-level items (including the entry
script's own `impl` blocks) are registered by a structurally separate
function, `evaluate_module_impl()` in `interpreter_eval.rs`. That function's
`Node::Impl` arm (pre-fix lines 935-1010) had the identical untagged
`method_with_impl_driver_attrs(...)` pattern at all 4 of its method-copy call
sites — none of them called `tag_function_module_owner` (or anything
equivalent), so entry-script impl-block methods got **no owner tag at all**,
not even the `"<entry>"` sentinel that the same function's `Node::Function`
arm (~line 505) deliberately assigns to entry-script free functions.

This is a strictly worse failure mode than RC1's or RC2's: `<entry>` is at
least a stable, distinct fallback bucket. With no tag whatsoever,
`function_module_owner()` (`interpreter_call/core/function_exec.rs`) returns
`None`, and `CURRENT_EXEC_MODULE` (per its `execute_function_body`
save/restore) is left holding whatever the **caller's** frame had — so an
entry-script impl-block method invoked from inside another module's function
body can have its coverage rows attributed to that OTHER module's file, not
merely to `<entry>`.

### Enumeration

`grep -rn 'method_with_impl_driver_attrs(' src/compiler_rust/compiler/src/`
across the whole crate returns exactly 3 families:

- `interpreter_eval.rs:935-1010` (`Node::Impl` in `evaluate_module_impl`,
  the script-eval / entry-file path) — **4 sites, all untagged pre-fix**:
  the `impl_methods` push, the `GLOBAL_IMPL_METHODS` extend, the
  `classes.get_mut(&type_name)` extend, and the static-method-from-impl-block
  loop. Fixed this pass.
- `interpreter_module/module_evaluator/evaluation_helpers.rs` (`Node::Impl`
  in `register_definitions`, the import-module path) — 6 sites, already
  fixed by RC1 (`b6a43042`).
- `hir/lower/module_lowering/module_pass.rs` (3 sites) — HIR lowering for the
  AOT/native pipeline, not the interpreter's `FUNCTION_MODULE_OWNER`/
  `CURRENT_EXEC_MODULE` coverage-attribution mechanism at all (no such
  concept exists in HIR lowering); out of scope for this defect family.

### Fix

Mirrors RC1's `tagged_method` closure shape. `interpreter_eval.rs`'s
`Node::Impl` branch has no `module_ident` (the script-eval path never had a
module identity concept), so it uses the same `"<entry>"` literal sentinel
the co-located `Node::Function` arm already uses for entry-script functions —
giving entry-script impl methods the same distinct-but-stable fallback bucket
that free functions and RC2 already have, instead of silently inheriting a
foreign `CURRENT_EXEC_MODULE`. The static-method loop additionally records
into the pointer-keyed `FUNCTION_MODULE_OWNER` thread-local directly (inlined,
since `evaluation_helpers.rs`'s `record_function_owner` helper is private to
that module), matching RC1's belt-and-suspenders pattern for that site.

Changed: `src/compiler_rust/compiler/src/interpreter_eval.rs` — imports
`tag_function_module_owner`; `Node::Impl` arm's 4 method-construction sites
now route through a `tagged_method` closure.

### Verification

Confirms the "strictly worse than `<entry>`" prediction above, not merely the
`<entry>`-sentinel case: a 2-file repro where the entry spec (`rc1sib_spec.spl`)
defines `class Widget` / `impl Widget: fn compute(self, x)` with an `if x > 0`
decision, and an imported module (`helper_mod.spl`, `fn call_it(w) ->
w.compute(5)`) calls into it — i.e. the impl method's body executes from
*inside an imported module's stack frame*, the scenario that inherits a
foreign `CURRENT_EXEC_MODULE` pre-fix. Run via `simple test rc1sib_spec.spl
--no-session-daemon --sequential` under `SIMPLE_COVERAGE=1`:

- OLD (`bin/release/x86_64-unknown-linux-gnu/simple`, deployed seed, pre-fix):
  `compute`'s line-9 hit and its line-8 `if` decision are both attributed to
  `helper_mod.spl` — the CALLER's file, not the entry spec that defines
  `compute`. `total_files: 1` (the entry file's own line dropped out of the
  report entirely, folded into the wrong file).
- NEW (`src/compiler_rust/target/release/simple`, this fix): both rows
  correctly key to the entry spec file's own path (its `.spipe_cov_*` staged
  copy); `total_files: 2`, `helper_mod.spl` correctly shows only its own
  line 2.

Raw artifacts: `/tmp/cov_probe_rc1sib/old.sdn` (OLD), `/tmp/cov_probe_rc1sib/new.sdn`
(NEW), repro sources in `/tmp/cov_probe_rc1sib/spec_test/`.

`cargo build --release` (full workspace, this session's build slot): 0 errors,
pre-existing warnings only, `Finished \`release\` profile [optimized] target(s)
in 4m 16s`.

## Evidence retained

- `/tmp/probe_ebc.sdn` — pre-fix artifact from
  `engine2d_baremetal_core_spec.spl`, backing the 73-row/143-boundary claims
  above.
- Post-fix probe (old binary vs. new binary, same spec) recorded in
  `doc/09_report/ui/testing/coverage_entry_placeholder_fix_verified_2026-08-08.md`
  if the build succeeded this session; otherwise this doc stands alone as the
  diagnosis.

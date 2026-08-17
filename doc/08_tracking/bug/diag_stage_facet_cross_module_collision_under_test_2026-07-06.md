# std.diag dbg_stage() aborts under `bin/simple test` when co-compiled with the browser_engine/host_compositor module graph

**Date:** 2026-07-06
**Severity:** medium — blocks writing `bin/simple test` specs that prove
real `dbg_stage()` emission for task #15 remainder item 3 ([browser] stage
logs); does not affect `bin/simple run` or production behavior.
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
2026-08-01 the original repro no longer reproduces on the Rust seed and the
facet-on spec coverage is restored, but the name-keyed registry is unchanged and
still armed; the collision *detector* was widened to public functions and
methods. See "Resolution pass 2026-08-01" at the bottom.

## Symptom

Any spec file that combines:
1. `use std.spec.*` (the wildcard every `*_spec.spl` file uses for
   `describe`/`it`/`expect`)
2. an import that pulls in the browser_engine/`os.compositor.host_compositor_entry`
   module graph (directly, or transitively via `app.ui.browser.app`'s own
   `use os.compositor.host_compositor_entry.{...}`)
3. `std.diag.dbg_force_facet(...)` forcing any facet on
4. a real `std.diag.dbg_stage(...)` call while that facet is on

aborts the whole `it` block with:

```
semantic: type mismatch: comparing string with integer
```

This reproduces under `bin/simple test <spec>` regardless of how many names
are explicitly imported from `std.diag` (a full explicit import list —
matching `test/01_unit/lib/nogc_sync_mut/diag_spec.spl`'s working set —
does NOT avoid it once the host_compositor/browser_engine graph is also
present). It does **not** reproduce under
`SIMPLE_EXECUTION_MODE=interpret bin/simple run <script>.spl` with the
identical imports and logic — confirmed via direct A/B repro (same file
content, `run` succeeds, `test` aborts).

## Minimal repro

```
use std.spec.*
use os.compositor.host_compositor_entry.{HostBackendKind}
use std.diag.{dbg_stage, dbg_force_facet, dbg_diag_reset, dbg_stage_history}

describe "repro":
    it "aborts":
        dbg_diag_reset()
        dbg_force_facet("stage")
        dbg_stage("probe", "hello")
        expect(dbg_stage_history().len()).to_be_greater_than(0)
```
Run via `SIMPLE_EXECUTION_MODE=interpret bin/simple test <this file>` →
aborts with the error above. Dropping either the `os.compositor.host_compositor_entry`
import or the `std.spec.*` wildcard (replacing it with the concrete
`describe`/`it`/`expect` imports it re-exports) makes it pass — confirmed
by isolating each ingredient independently during this investigation.

## Why it matters

Same bug class already ledgered under
`doc/08_tracking/bug/interp_cross_module_struct_field_collision_2026-07-04.md`
and the `_clamp_byte`/`_hex_pair`/`_read_u32_le`
`compiler_cross_module_private_symbol_collision` warnings printed at the
top of every `bin/simple test` run in this repo: when many modules
co-compile into one test unit, some private/public top-level symbol
(function or enum) collides across modules and the wrong co-compiled
definition is dispatched. Here the collision lands inside `dbg_stage()`'s
own body (a ~15-line function with no string/int comparisons in its
source), so the miscompiled callee is almost certainly something `dbg_stage`
calls transitively (`_emit` → `lib.log.log_dispatch_text` /
`subsys_from_scope`) picking up an unrelated same-named helper from the huge
browser_engine graph.

A related, separately-confirmed instance in the same graph: `enum
Capability` is defined 4x across `src/lib/common/ui/capability.spl` and
`src/lib/nogc_sync_mut/{security/enforcement,fs_driver,storage}/capability.spl`;
calling `BrowserApp.run_once()` (which renders a real frame) aborts with
`semantic: unknown variant or method 'Mouse' on enum Capability` under both
`run` and `test`. Also witnessed in the same investigation (test-mode
only): `enum LayoutKind` is defined 2x
(`src/lib/common/ui/widget_kind.spl` vs
`src/compiler/30.types/_TypeLayout/layout_core.spl`), surfacing as
`semantic: unknown variant or method 'Vbox' on enum LayoutKind`.

## Workaround used (task #15 remainder item 3)

`test/01_unit/app/ui/browser_shared_wm_and_stage_log_spec.spl` proves the
default-off contract (facet off → zero dbg_stage_history entries, which
does not touch the crashing path) and documents — with a manual
`bin/simple run` verification recorded in its header comment — that the
four `[browser]` stages (`parse_start`/`parse_done`/`backend_create_start`/
`backend_create_done`) fire correctly with the facet forced on. It does not
include a `bin/simple test`-executable assertion for the facet-forced-on
case, since that combination cannot currently pass.

## Next step

Find where `dbg_stage`'s transitive callees (most likely `lib.log`'s
`log_dispatch_text`/`subsys_from_scope`, or a shared string-processing
helper) resolve unqualified/private symbol names when co-compiled with the
browser_engine graph, and make resolution key off of the declared
module+type rather than name (same architectural fix needed for the
`Capability`/`LayoutKind` enum collisions and the already-ledgered `Style`
vs `CellStyle` struct collision). This is compiler/interpreter work, not
`src/app/ui.browser/**`.

---

# Triage 2026-08-01 — product defect, NOT test isolation

Read-only static analysis (no build/run; filesystem is in a btrfs metadata
ENOSPC state). Claims below are each backed by a `file:line` in-tree.

## Verdict

**Genuine product defect in the compiler's import flattening + bare-name
symbol registry. NOT an artifact of shared state between specs.** Nothing is
carried between spec files. Adding `use std.spec.*` changes the *content of
the single compilation unit* (more modules get flattened into one flat
symbol table), it does not introduce cross-spec state. The distinction
matters because the two failure classes demand opposite fixes and this one
must NOT be "fixed" by test isolation.

## Mechanism, quoted from the compiler itself

`src/compiler_rust/compiler/src/pipeline/module_loader.rs:1302-1312`:

> Functions resolve by bare name (interpreter `HashMap<String, FunctionDef>`;
> codegen `func_ids`, last-write-wins), so once the import flattening merges
> two same-named definitions, a call may silently dispatch to the wrong one —
> nil / garbage in the interpreter, NULL-deref SIGSEGV under Cranelift

That is the registry. It is **per-compilation-unit and flat**, keyed on the
bare name, populated by import flattening — it is *not* a process-wide table
that leaks between specs, and it is *not* a thread-local. The same warning
emitter (`warn_duplicate_private_signatures`,
`src/compiler_rust/compiler/src/pipeline/module_loader.rs:1314`) is what
prints the `compiler_cross_module_private_symbol_collision` lines quoted in
the "Why it matters" section above.

So: **yes, this bug is that global registry seen from the diagnostics side.**
Same registry, same last-write-wins rule, different victim module.

## Which engine actually produced the reported error

The quoted string is `type mismatch: comparing string with integer`. That
exact wording exists in **one place only** —
`src/compiler_rust/compiler/src/interpreter/expr/ops.rs:970, 1002, 1034, 1066`
(the Rust seed interpreter). The pure-Simple interpreter emits a *different*
string, `"type error: comparing string with integer — use .ord() ..."`
(`src/compiler/10.frontend/core/interpreter/ops.spl:141,159,177,195`;
`src/compiler/35.semantics/semantics/binary_ops.spl:192-195`).

Consequence: **the repro was executed by the Rust seed**, consistent with
`simple test` delegating to a seed child. The behaviour of the pure-Simple
compiler on this repro is therefore **UNVERIFIED** and must not be assumed
identical. Any future re-repro must record which binary ran.

Second constraint from the same source: the error can only be raised by the
**ordering** operators `Lt/Gt/LtEq/GtEq` on a `(Str, Int)` pair
(`ops.rs:960-1010` — `Eq`/`Ne` fall through to `Value` equality and never
raise it). So the mis-dispatched callee must reach a literal `<`/`>`, not a
`==`. That is a strong filter and it eliminates most of the call graph:
the only ordering comparisons reachable from `dbg_stage` are
`src/lib/nogc_sync_mut/diag.spl:153` (`_g_stage_ring.len() > _RING_CAP`),
`src/lib/log.spl:173` (`level >= effective_level(subsys) and level < LOG_OFF`),
`src/lib/log.spl:613,615,622` and `src/lib/log.spl:630,633`.

## What the original hypothesis got wrong (disproven)

The "Next step" section above guesses the collider is `_emit`,
`log_dispatch_text` or `subsys_from_scope`. Checked:

- `log_dispatch_text` — **1** definition repo-wide (`src/lib/log.spl:652`).
- `subsys_from_scope` — **1** definition repo-wide (`src/lib/log.spl:695`).
- `_read_env_once` — **1** (`src/lib/nogc_sync_mut/diag.spl:74`).
- `_deadline_check_all` — **1** (`src/lib/nogc_sync_mut/diag.spl:277`).
- Every module-level global on the path is unique repo-wide: `_RING_CAP`,
  `_g_diag_file`, `_g_global_level`, `_LOG_FILE_PATH`, `GLOBAL_LOG_LEVEL`,
  `LOG_TEXT_INTERN_CAP`, `_g_text_intern_next`, `_g_backend_count`,
  `_g_panic_mode` — 1 definition each.
- `_emit` has 3 definitions —
  `src/app/process/main.spl:21` `(result: AccessResult, as_json: bool) -> i64`,
  `src/lib/nogc_sync_mut/log.spl:116` `(line: text)`,
  `src/lib/nogc_sync_mut/diag.spl:140` `(level: i64, line: text)` —
  and the second one is a tempting fit (bind `line = LOG_INFO` i.e. an Int).
  **But it cannot be reached.** `src/lib/nogc_sync_mut/log.spl` has **zero**
  importers under any spelling: `use std.log` resolves to `src/lib/log.spl`,
  because the direct `stdlib_root/<parts>.spl` probe at
  `module_loader.rs:418-424` fires before the tier-subdirectory search at
  `module_loader.rs:450-470`. (`src/std` is a symlink to `lib`, verified.)
  So `_emit` is a latent landmine, not this bug's collider.

Closure scan: I enumerated every `_`-prefixed top-level helper across the
**275-module transitive import closure** of
`os.compositor.host_compositor_entry` (plus `std.diag` and `lib.log`), after
de-duplicating the `src/std -> lib` symlink. The only bare name with two
*differing* signatures in that closure is `_pci_ecam_base`
(`src/os/drivers/pci/pci.spl`, both definitions in one file, arch-gated) —
irrelevant.

### `std.spec.*` closure — scanned

`use std.spec` resolves to `src/lib/nogc_async_mut/spec/__init__.spl` (tier
search order at `module_loader.rs:450-457` puts `nogc_async_mut` first). That
package is **self-contained**: 6 files
(`__init__/mod/condition/decorators/env_detect/feature_doc.spl`) whose only
`use` statements are `std.spec.*` siblings. It contributes 28 bare top-level
function names. Cross-checked repo-wide, the ones with a second definition
elsewhere are `check`, `check_msg`, `pending`, `skip`, `skip_it`, `step`,
`generate_feature_doc`, `get_all_features`, `get_features_by_category`,
`register_feature`. Notably `skip` has 4 (`src/lib/nogc_sync_mut/spec.spl:216`
`(name: text, reason: text)` vs `src/lib/{nogc_sync_mut,gc_async_mut,
nogc_async_mut}/src/testing/gpu_helpers.spl:56` `(reason: text)`) and `step`
has a `(description: text)` vs `(edge: f32, x: f32) -> f32` pair. **None of
those are on `dbg_stage`'s call path**, so none explains the repro directly.

**STILL UNIDENTIFIED — narrowed shortlist.** The strongest remaining
candidate is the *last* line of the repro, not `dbg_stage` itself. The
document above never established which statement aborts. Two facts make
`expect(...).to_be_greater_than(0)` the prime suspect:

- `src/lib/nogc_sync_mut/spec.spl:613-620`, `ExpectHelper.to_be_greater_than`,
  is `if self.value <= expected:` — an `LtEq` on `value: any`
  (`src/lib/nogc_sync_mut/spec.spl:605` declares `value: any`). That is
  exactly the one operator class that can raise this error, and the `any`
  erasure is what lets a wrongly-dispatched Str reach it.
- `src/lib/nogc_sync_mut/spec.spl:525` and `:530` declare **two same-named
  overloads** of `expect` in one file — `(value: bool)` and `(value)`. Under
  the bare-name `HashMap<String, FunctionDef>` this is the same last-write-wins
  hazard, and it is the known same-name-overload corruption family.

Confirming this needs one runtime observation that static reading cannot
supply: which statement aborts. Do that with a bisected repro (drop the
`expect` line; keep `dbg_stage`) rather than a full suite run.

### Why "no collision warning was printed" proves nothing

`warn_duplicate_private_signatures` skips any name that does not start with
`_` — `src/compiler_rust/compiler/src/pipeline/module_loader.rs:1321-1323`:

> if f.name.contains('.') || !f.name.starts_with('_') { continue; }

and it skips qualified method names (`Type.method`) entirely. So **public
free functions and all methods collide silently, with no diagnostic at all**,
while resolving through the same last-write-wins table. `expect`,
`to_be_greater_than`, `skip` and `step` are all in that unwarned class. The
absence of a `compiler_cross_module_private_symbol_collision` line for this
repro is therefore not evidence that nothing collided — it is a gap in the
detector. Widening that detector to public frees and to methods is cheap and
should precede the resolver rework.

## Can it occur outside a test run?

**Yes.** The trigger is graph composition, not the harness. The production
browser app already co-compiles the two halves:
`src/app/ui.browser/app.spl:16` `use std.diag.{dbg_stage}` together with
`src/app/ui.browser/app.spl:18`
`use lazy os.compositor.host_compositor_entry.{...}`. The only reason `run`
does not currently abort is that the *specific* colliding name is contributed
by `std.spec.*`; any future import that pulls the same name into a production
unit reproduces it with no test runner in sight.

Independent corroboration inside this very document: the `Capability` and
`LayoutKind` enum collisions recorded at lines 74-82 abort under **both**
`run` and `test`. Same family, same registry, and they are demonstrably not
harness artifacts.

## Ruling out the two "it's the harness" theories

- *Shared test database / parallel `simple test`.* Not applicable. The
  failure is a compile/dispatch-time semantic error raised while evaluating
  the `it` block, not a data-corruption symptom, and the repro is a single
  spec file. No test-DB path is on `dbg_stage`'s call graph.
- *Cross-spec residual state.* `std.diag`'s state (`_g_env_read`,
  `_g_facet_*`, `_g_stage_ring`) is module-global and would only matter
  within one process; the repro calls `dbg_diag_reset()` first, and the
  failure is a type error, not a stale-value error.

## Change I would make (NOT made)

1. **Do not add test isolation. Do not rename a helper.** Renaming fixes one
   instance and leaves the registry name-keyed — that is the sibling-leaving
   pattern this repo has already been burned by.
2. Key the interpreter function registry on **(module path, bare name)**
   rather than bare name, resolving a call site against its *own* module
   first and only then against explicitly-imported names. Concretely: replace
   the `HashMap<String, FunctionDef>` described at `module_loader.rs:1305`
   with a module-qualified map plus a per-module import view. The same change
   covers the enum (`Capability`, `LayoutKind`) and struct (`Style` vs
   `CellStyle`) instances of this family, which is the point — one fix, whole
   family.
3. **Widen the detector first** (cheap, independent of (2)): drop the
   `!f.name.starts_with('_')` and `f.name.contains('.')` skips at
   `module_loader.rs:1321-1323` so public free functions and methods are
   checked too, and add same-file same-name overloads (`expect` at
   `src/lib/nogc_sync_mut/spec.spl:525,530`). Then promote it to a **hard
   error under a gate** once (2) lands, so regressions cannot re-enter
   silently. Doing this before (2) will very likely name the collider
   outright.
4. Mirror the fix in the pure-Simple resolver, not just the seed — the seed
   is bootstrap-only and the pure-Simple path here is currently unverified.

## Masking risk — the thing that must not be lost

Because this is a product defect, "fixing the test" is the dangerous move,
and there are three concrete ways to mask real defects here:

- **Masking A (the live one).** The workaround already in the tree —
  `test/01_unit/app/ui/browser_shared_wm_and_stage_log_spec.spl` asserting
  only the facet-*off* contract — means the facet-*on* emission path has **no
  automated coverage at all**. The `[browser]` stage logs are currently
  proven only by a hand-run `bin/simple run` recorded in a header comment.
  That is exactly the shape of evidence this repo treats as non-evidence. Any
  regression in `dbg_stage` emission lands silently today.
- **Masking B.** If someone "resolves" this by renaming `_emit` (or whichever
  helper turns out to collide) to a unique name, the spec goes green while
  the name-keyed registry is untouched. Every other same-named pair in the
  repo stays armed, and the next one surfaces as a NULL-deref SIGSEGV under
  Cranelift rather than a readable semantic error — a strictly worse failure
  mode than the current one (`module_loader.rs:1306-1308` says so
  explicitly).
- **Masking C.** If someone "resolves" this by dropping `use std.spec.*` in
  favour of concrete imports (the repro shows that makes it pass), the spec
  goes green *and* the compilation unit silently stops covering the
  browser+spec composition. The bug is then invisible until production.

None of these three fix anything. The green they produce is false green.

---

# Resolution pass 2026-08-01 — detector widened, repro no longer reproduces

**Status change: OPEN → the original repro no longer reproduces; the underlying
name-keyed registry is UNCHANGED and still armed.** Read both halves of that
sentence — the second half is why this file stays open.

## Engine measured

`src/compiler_rust/target/bootstrap/simple test <spec>` (the Rust seed). It
delegates the spec run to `src/compiler_rust/target/debug/simple` — the log line
`child binary: .../target/debug/simple` records this. That is the engine that
owns the `type mismatch: comparing string with integer` wording, so it is the
right engine to re-measure on. **The pure-Simple binary could not be measured:
the deployed `bin/simple` at HEAD has no `test` subcommand (`error: unknown
command 'test'`), a separate known defect. The pure-Simple path remains
UNVERIFIED, exactly as the triage above said.**

## Re-measurement result

Three escalating repros, all run from the repo root:

1. The minimal 4-ingredient repro from the "Minimal repro" section — **passes**
   (`Results: 1 total, 1 passed, 0 failed`), and `[probe] stage hello +0ms` is
   emitted, i.e. `dbg_stage` really ran.
2. Same plus `use app.ui.browser.app.{BrowserApp, browser_shared_wm_config}` —
   **passes**.
3. The full in-tree spec `test/01_unit/app/ui/browser_shared_wm_and_stage_log_spec.spl`
   with the previously-omitted facet-forced-on `it` restored — **4 total, 4
   passed**.

The abort is gone on this engine. No claim is made about *which* change fixed
it; nothing in this pass targeted it.

## Masking A retired

`test/01_unit/app/ui/browser_shared_wm_and_stage_log_spec.spl` now carries the
facet-**on** assertion as a runnable `it`
("records stage entries when the SIMPLE_DIAG stage facet is forced on"),
replacing the comment that stood in for it. The facet-on emission path had zero
automated coverage for a month; it now has an executing oracle.

Verified to be a real oracle, not a false green: flipping
`to_be_greater_than(0)` to `to_be_greater_than(9999)` in a scratch copy fails
with `expected 1 to be greater than 9999`, `Results: 4 total, 3 passed, 1
failed`, exit 1.

Masking B and C were both avoided: nothing was renamed to make the spec pass,
and `use std.spec.*` is still there, so the browser+spec composition is still
covered.

## The class fix that WAS made — detector blind spots closed

The gap identified in "Why 'no collision warning was printed' proves nothing" is
now closed on both engines. Three skips were removed:

| Where | Was skipped | Now |
|---|---|---|
| `src/compiler_rust/compiler/src/pipeline/module_loader.rs` `warn_duplicate_private_signatures` | every name not starting with `_`; every name containing `.` | all top-level functions; message classifies `private helper` / `public function` / `method` |
| `src/compiler_rust/compiler/src/pipeline/module_loader.rs` `warn_cross_impl_method_collisions` (new) | cross-impl-block method collisions had **no detector at all** — `find_method_arity_collisions` only looks inside one impl block | same `Type.method` key contributed by 2+ separate impl blocks with differing signatures → `[compiler_cross_module_method_collision]` |
| `src/compiler/10.frontend/core/interpreter/eval_tables.spl` `_ftr_warn_collision` | `not name.starts_with("_")`; `name.contains("__")` (methods) | both removed; same three-way classification |

The new method check is not dead code: a 12-line probe (two `impl Foo` blocks in
two co-compiled files, `fn tag() -> text` vs `fn tag(n: i64) -> i64`) emits
`warning: method `Foo.tag` is defined by 2 separate co-compiled impl blocks with
2 differing signatures ((?)->text vs (?,i64)->i64) ...`.

This is the class fix the triage asked for (item 3 of "Change I would make"). It
is a **diagnostic**, not the resolver rework — item 2 (key the registry on
(module path, bare name)) is still outstanding and is still the real fix.

## Colliders it named immediately — all previously INVISIBLE

Running the browser+`std.spec.*` compilation unit with the widened detector
surfaces five public-function collisions that produced **no diagnostic at all**
before this change:

```
public function `skip`           ([text],[text],[text],[text],[text],text,[text],[text],Dict<text,text>,[text],bool,[text],text)->Function  vs  (text,text)->()
public function `shell`          (text)->ProcessResult    vs  (text)->ShellResult          [3 definitions]
public function `shell_output`   (text)->text             vs  (text,text)->text            [3 definitions]
public function `file_read_bytes`(text)->[i64]            vs  (text)->[u8]
public function `dir_remove_all` (text)->bool             vs  (text)->i32
```

`skip` is the one the triage above flagged from the `std.spec.*` closure
(`src/lib/nogc_sync_mut/spec.spl:216` `(name, reason)` vs the gpu_helpers
`(reason)` family). It is armed inside the spec harness itself, on a
last-write-wins slot, with a 13-parameter closure-returning sibling. A separate
run over `src/compiler/10.frontend/core/interpreter/eval_tables.spl`'s closure
also named `write_file` (`(String,String)->Result<Int,String>` vs
`(text,text)->bool`).

Noise check: five findings in a 275-module unit, zero method findings — the
widened detector is signal, not a flood.

## What is still open

- **The registry is still bare-name keyed.** Item 2 above (module-qualified
  resolution) is not done. Every pair listed here, plus the `Capability` /
  `LayoutKind` / `Style`-vs-`CellStyle` instances, is still armed.
- **The five named colliders are not renamed.** Deliberately: renaming them is
  Masking B if presented as the fix. They are recorded here so the follow-up is
  findable by name.
- **Pure-Simple engine unverified.** `bin/simple` has no `test` subcommand at
  HEAD. The pure-Simple mirror of the detector widening is code-reviewed and
  parses (lint output byte-identical to the pre-change baseline, which itself
  times out on this file — a pre-existing, unrelated hang), but has not been run.
- **Promotion to a hard error under a gate** (the rest of item 3) is not done
  and should wait until item 2 lands.


## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STILL-OPEN (diagnostic-only mitigation present)

A collision WARNING now exists near `src/compiler/10.frontend/core/interpreter/eval_tables.spl:243`:

```spl
        _ftr_collision_warned.push("samesig:{name}")
        val same_kind = _ftr_collision_kind(name)
```

but it warns rather than namespacing the registry; the flat bare-name dispatch
remains. ROOT-CAUSE FAMILY: flat bare-name registries (see
bare_name_registry_collision_trigger_conditions_2026-07-30,
duplicate_type_name_collision_audit_2026-07-17).

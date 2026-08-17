# Deletion evidence package: `src/app/interpreter/`

> **OWNER DECISION PACKAGE — read section 0 only. Everything below it is the
> supporting detail, kept verbatim.** No deletion has been performed and none
> will be without an owner decision. The companion doc
> `app_interpreter_tree_declared_removed_but_still_on_disk_2026-08-10.md` holds
> the original diagnosis; section 0 folds its conclusions in so this file is a
> single read.

## 0. Decision package (re-measured 2026-08-17, current `HEAD` working tree)

### 0.1 What is on disk

| Metric | Value |
|---|---|
| Path | `src/app/interpreter/` |
| Files on disk | **100** (99 `.spl` + 1 non-`.spl`) |
| Files tracked in git | **99** — `git ls-tree -r --name-only HEAD -- src/app/interpreter/` |
| Untracked residue | **0** (`git status --porcelain -uall` on the path is empty) |
| Size on disk | **1.1 MB** (`du -sh`) |
| Source lines | **25,232** across the 99 `.spl` files |
| Files using the rejected `from X import {...}` form | **62 of 99** (was reported as 61 in 2026-08-11; re-counted today) |
| Repo total tracked files | 114,545 — a 99-file removal is 0.086%, inside the tree-size guard's +/-0.15% band, so **no `--expect-files` override is needed** |

### 0.2 What references it (complete, `git grep` over `HEAD`, code+scripts only)

**Real compile-time imports from outside the tree: ZERO.**
`git grep -n "use app\.interpreter" HEAD -- '*.spl' | grep -v src/app/interpreter/`
returns **0 lines**. The only `use app.interpreter...` statements in the repo are
inside the tree, in `collections/persistent_dict/*.spl`, importing each other.

The 15 non-tree files that mention the path at all, classified:

| Class | Files | Breaks on deletion? |
|---|---|---|
| **Real runtime dependency — content read** | `test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl:41,48` (`read_file("src/app/interpreter/core/watchdog.spl")`, asserts on substrings) | **YES** — file-not-found. Must be edited in the same change. |
| **Real runtime dependency — subprocess** | `test/03_system/feature/interpreter/runtime_error_stack_spec.spl:73` (`run_interpreter(["src/app/interpreter/main.spl", script])`; :30 is a commented twin) | **Already RED today** — the tree does not compile, so this cannot pass now. Deletion changes the failure mode, not the colour. |
| **Path-string exclusion rules** (reference the path only to skip it) | `scripts/check/check-ui-backend-isolation.shs`, `src/app/doc_coverage/scanner/file_scanner.spl` | No — become dead exclusions; optional cleanup |
| **Comments / prose only** | `src/app/__init__.spl` (the "REMOVED" declaration), `src/compiler/10.frontend/core/interpreter/mod.spl` (the "DELETED 2026-02-10" declaration), `src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl`, and 7 spec files incl. both `generator_intensive_spec.spl` mirrors and both `compiler_interpreter_integration_spec.spl` mirrors | No |
| **Tests a string constant, not the tree** | `test/03_system/app/ui/feature/backend_isolation_gate_spec.spl` (asserts the exclude-glob text) | No |

### 0.3 If REMOVED

* Compile-time breakage: **none** (zero external imports; the tree does not
  compile as a unit today anyway — 62/99 files use `from X import`, which the
  compiler rejects with `semantic: variable 'from' not found`).
* Must be edited in the same commit: the two `it` blocks in
  `watchdog_manager_spec.spl`, and `runtime_error_stack_spec.spl:73`.
* Gains: 100 files / 1.1 MB / 25,232 lines off every `src/app/` walk;
  `async_runtime/generators.spl` becomes importable so both
  `generator_intensive_spec.spl` mirrors can drop their hand-copied
  `GeneratorState` enum; two source comments stop contradicting the filesystem.
* Risk actually accepted: nobody has read all 99 files to prove each is a dead
  duplicate rather than a unique implementation. What IS proven is the weaker
  but decision-relevant fact that **nothing outside the tree can reach any
  symbol in it today**. Recovery path if wrong: `git log`.

### 0.4 If KEPT

* Nothing breaks — the status quo is stable, because nothing depends on it.
* Ongoing costs: the two "REMOVED"/"DELETED" source comments stay false; 25,232
  lines of uncompilable source stay in every scan, census, and lint sweep; the
  two exclusion rules stay load-bearing; the generator-import unblock stays
  unavailable and both spec mirrors keep their duplicated enum.

### 0.5 Recommendation

**Delete**, in one commit that also edits `watchdog_manager_spec.spl` and
`runtime_error_stack_spec.spl`. The deciding fact is that two independent source
comments authored months before any of this analysis already declare the tree
removed, and the measurement agrees with them on every axis that matters:
zero external imports, zero untracked residue, and a tree that does not compile.
Keeping it preserves no capability — it only preserves the contradiction.

**If the owner wants the stronger guarantee first**, the outstanding work is a
file-by-file read of all 99 for logic absent from
`src/compiler/10.frontend/core/interpreter/` and `src/lib/nogc_async_mut*`. That
has not been done and is not claimed.

---


**Status:** EVIDENCE ONLY — no deletion performed. For the repo owner's decision.
**Date:** 2026-08-11
**Builds on:** `doc/08_tracking/bug/app_interpreter_tree_declared_removed_but_still_on_disk_2026-08-10.md`
(hereafter "the prior doc"), which established the core diagnosis. This doc adds
the full inventory, a repo-wide inbound-reference census with a positive
control, and a concrete deletion procedure — the parts the prior doc explicitly
deferred as "its own reviewed change."

## 1. Inventory

`git ls-tree -r --name-only origin/main -- src/app/interpreter/` returns
exactly **99 files**, confirming the number in the prior doc and the task
brief. Full list captured at commit `78a24b4d143903f30f84a696f595c9947afd043b`
(current `origin/main` tip at time of this scan). Notable subpackages:
`ast_convert_expr.spl`, `main.spl`, `core/` (incl. `watchdog.spl`,
`execution_guard.spl`), `expr/` (incl. `advanced.spl` — the live `eval_spawn`),
`async_runtime/` (incl. `actors.spl`, `generators.spl`, `mailbox.spl`,
`actor_heap.spl`, `actor_scheduler.spl`), `collections/persistent_dict/`,
`collections/persistent_vec`, `lazy/`, `perf/`, `helpers/`, `utils/`, `ffi/`,
`module/`.

## 2. Inbound reference census

**Method note (positive control):** repo-wide `grep -r` over `.` timed out
under the disk I/O load described in the task brief (2 min, no output) —
exactly the "timed-out grep returns empty" trap from prior sessions. Switched
to `git grep <pattern> origin/main -- <globs>`, which reads packed git objects
rather than walking the working tree, and returned in seconds. Positive
control: `git grep -n "app\.interpreter" origin/main -- '*.spl' '*.shs' '*.md'`
returned 43 hits including known-present lines (e.g. the removal comment in
`src/app/__init__.spl:33` itself), proving the search path is live, not
silently empty.

### 2a. Dotted `app.interpreter` form (43 hits total, repo-wide)

All 43 hits, minus the ones that are themselves inside the tree
(`persistent_dict/*.spl` internal cross-references, 8 hits), leave **35 hits
outside the tree — every one of them is prose**: doc reports
(`doc/09_report/**`), tracking docs (`doc/08_tracking/bug/**`), design docs
(`doc/05_design/**`), the `.spipe` audit-state file, and the two spec header
comments (`test/01_unit|unit/lib/nogc_async_mut/generator_intensive_spec.spl:31`)
that themselves quote the "REMOVED" declaration. **Zero real `use
app.interpreter....` import statements exist anywhere outside the tree.** The
only such statements found repo-wide are inside the tree's own
`collections/persistent_dict/*.spl` files, importing each other.

### 2b. Path-form `app/interpreter` (996 hits total, repo-wide; 217 distinct files outside the tree)

Breakdown by directory of the 217 outside-tree files: `doc/09_report` (82),
`doc/08_tracking` (68), `doc/06_spec` (21), `doc/01_research` (7),
`test/01_unit` (4), `scripts/check` (4), `doc/03_plan` (4), plus smaller
counts elsewhere. Classified the code/test/script hits (the only ones that
could matter functionally) individually:

| File | What it does | Class |
|---|---|---|
| `scripts/check/check-ui-backend-isolation.shs:50` | Glob-excludes `src/app/interpreter/ffi/**` from a UI/backend isolation scan | exclusion rule referencing the path, not a dependency on it |
| `scripts/check/classify-compiled-check-results.py:89` | `if path.startswith("src/app/interpreter/")` — special-cases results from this tree in a report classifier | path-string check, not a dependency |
| `scripts/check/test_tree_divergence_baseline.txt`, `ui_backend_isolation_baseline.txt` | Baseline files listing paths under this tree | data/baseline, not code dependency |
| `src/app/doc_coverage/scanner/file_scanner.spl:96` | `if path.contains("/src/app/interpreter/")` — likely excludes this tree from doc-coverage scanning | path-string check, not a dependency |
| `src/compiler/10.frontend/core/interpreter/mod.spl:21` | The second "already removed" declaration (see §3) | comment |
| `src/compiler/90.tools/migrate/tests.spl:107,198,199,450` | References `test/01_unit/app/interpreter` / `test/app/interpreter/*/*_spec.spl` — a **different, unrelated `test/` tree** with a coincidentally similar name, not `src/app/interpreter/` | namesake, not a dependency |
| `src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl:4` | Comment noting the app-layer module "never declares or calls" these externs | comment |
| `test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl:41,48` | **`read_file("src/app/interpreter/core/watchdog.spl")`** — reads file content and asserts on its text | **real runtime dependency (content-read, not compile-import)** |
| `test/01_unit/app/interpreter/ast_convert_expr_spec.spl:27` | Doc comment naming the implementation file; test body has no import of it (`use std.spec` only) | comment |
| `test/01_unit/compiler/semantics/preprocessor_when_cfg_spec.spl:130` | Comment | comment |
| `test/01_unit/lib/nogc_async_mut/generator_intensive_spec.spl:18,29` | Comments (quotes the prior doc's finding) | comment |
| `test/02_integration/`, `test/integration/compiler_interpreter_integration_spec.spl:28` | Comment listing interpreter as a component | comment |
| `test/03_system/app/ui/feature/backend_isolation_gate_spec.spl:16` | Asserts the *isolation script's exclude-glob string* contains `"src/app/interpreter/ffi/**"` — tests the exclusion rule itself, not the tree | tests a string constant, not the tree |
| `test/03_system/feature/interpreter/runtime_error_stack_spec.spl:73` | **Spawns `bin/simple run src/app/interpreter/main.spl <script>`** as a subprocess | **real execution dependency — but see §4, already non-functional** |

## 3. The two "already removed" declarations

- `src/app/__init__.spl:33` — `# - \`app.interpreter\` - REMOVED. Use
  \`core.interpreter\` instead for tree-walk`
- `src/compiler/10.frontend/core/interpreter/mod.spl:21` — `#    - Location:
  src/app/interpreter/ (removed)`, part of a larger comment block: "**Legacy
  Interpreter (DELETED 2026-02-10)**".

Both predate this scan and were not authored for it.

## 4. What breaks if deleted

**Compile-time: nothing.** Zero real `use app.interpreter...` statements exist
outside the tree (§2a). The package is also already uncompilable as a whole —
confirmed by the prior doc's Finding 2 (`from mailbox import {...}` — legacy
Python-shaped import form the compiler rejects with `semantic: variable 'from'
not found`) and independently reconfirmed here: 61 of 99 files use that form
(per task brief and prior doc), so no external compile unit can depend on any
name defined only inside this tree today, because the tree itself does not
compile as a unit.

**Runtime, two genuine hits, both already broken today, independent of
deletion:**

1. `test/03_system/feature/interpreter/runtime_error_stack_spec.spl` spawns
   `bin/simple run src/app/interpreter/main.spl <script>`. Since the package
   doesn't compile (§ above), this spec cannot currently pass — running
   `main.spl` triggers the same parse/semantic failure as everything else in
   the tree. Deletion changes its failure mode from "compile error inside
   `src/app/interpreter/`" to "file not found," but it is RED either way. Not
   a new regression, but the spec should be updated in the same change that
   deletes the tree (it will need a different failure-mode assertion, or
   removal, or a real target to point at).
2. `test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl`
   does `read_file("src/app/interpreter/core/watchdog.spl")` twice and asserts
   on substrings of the text (checking that `rt_watchdog_*` externs were moved
   OUT of it into `WatchdogManager`). This is a genuine content-pinning test
   that WILL break (file-not-found) if the file is deleted without updating
   the spec. **This is the one real "what breaks" item** — it needs its
   assertions rewritten or the two `it` blocks removed in the same change.

**Distinguishing "imports a name that also exists elsewhere" from "imports a
name only defined here":** no case of the former was found — there are no
real external imports at all (§2a). The `watchdog.spl` and `main.spl` hits are
not imports; they are file-content/subprocess probes from test code, which is
a different (and narrower) risk than a compile dependency.

## 5. What unblocks if deleted

- `src/app/interpreter/async_runtime/generators.spl` becomes importable
  (nothing else in its own package directory would block compilation of that
  directory once malformed siblings — `actors.spl` and the 61
  `from X import` files — are gone). This lets
  `test/01_unit/lib/nogc_async_mut/generator_intensive_spec.spl` (and its
  `test/unit/` twin) drop the mirrored `GeneratorState` enum and import the
  real one, per the prior doc's Follow-up section.
- Removes 99 files' worth of compile burden from every `simple build`/`test`/
  `lint` pass that walks `src/app/` (the compiler compiles every `.spl` in a
  package directory whether imported or not — the mechanism established in
  the prior doc's Finding 1).
- Removes a standing contradiction between two source comments (§3) and the
  actual filesystem state — anyone trusting those comments and then running
  `find src/app/interpreter` is currently misled.
- Simplifies the `scripts/check/check-ui-backend-isolation.shs` exclude-glob
  and `src/app/doc_coverage/scanner/file_scanner.spl` special-case (both
  reference this tree only to exclude it — dead exclusions once the tree is
  gone, though removing them is optional cleanup, not required by deletion).

## 6. Recommendation

**Recommend deletion**, with the two spec touch-ups from §4 included in the
same change (not deferred):

- Rewrite or remove the two `it` blocks in `watchdog_manager_spec.spl` that
  `read_file` the doomed path.
- Update or delete `runtime_error_stack_spec.spl`'s reference to
  `src/app/interpreter/main.spl` (it is already non-functional; deletion is a
  failure-mode change, not a new break, but leaving a spec that spawns a path
  that no longer exists is worse than one spawning a path that fails to
  compile).
- Land the generator-import unblock from §5 in the same or an immediate
  follow-up change so the win is captured, not just the deletion.

**Counter-argument, stated plainly:** the standing rule is "deleting a
reimplementation REROUTES rather than dedupes" — i.e. if this tree contains
logic not reimplemented elsewhere, deleting it doesn't eliminate that logic's
absence, it just makes the gap silent instead of documented. The prior doc
already did the legwork on this for the one file evaluated in depth
(`actors.spl`): its actor-registry logic (`static mut` id allocator +
process-global `Dict<u64, Actor>`) depends on `Channel<T>`, `Box<T>`,
`Duration`, `Expr`, `MatchArm`, and `interp.current_actor()` — none reachable
as real Simple types — and the live `eval_spawn` the interpreter actually
dispatches to already lives at `src/app/interpreter/expr/advanced.spl:181`,
making `actors.spl`'s copy a dead duplicate, not a unique implementation. That
argument was made file-by-file for one file, not exhaustively for all 99. This
scan did **not** re-verify, file-by-file, that every one of the other 98 files
is similarly a dead duplicate or unreachable rather than a unique
implementation — it verified only that **nothing outside the tree can reach
any of them today** (§2a/§4), which is the deletion-safety question, not the
"is anything inside irreplaceably unique" question. If the owner wants that
stronger guarantee before deleting, it requires a second pass reading each of
the 99 files for logic not present in `src/compiler/10.frontend/core/interpreter/`
(the stated replacement) or `src/lib/nogc_async_mut*`. Given the tree is
already unbuildable as a whole and has been declared dead by two independent
source comments predating this scan, the pragmatic recommendation is delete
now and treat any future "we needed that" as a `git log` recovery, not a
reason to keep 99 uncompilable files on disk indefinitely.

## 7. Deletion procedure

1. In the same commit: `git rm -r src/app/interpreter/` (99 files) plus the
   two spec edits from §6, plus (optional) removing the now-dead exclusion
   rules in `check-ui-backend-isolation.shs` and `file_scanner.spl` — or leave
   those as harmless residue and file a small follow-up.
2. Run the standard pre-push guards:
   - `sh scripts/check/check-no-conflict-tree-push.shs`
   - `sh scripts/check/check-no-conflict-markers-push.shs`
   - `sh scripts/check/check-tree-size-push.shs`
   - `sh scripts/check/check-test-tree-divergence.shs --ref <NEW>`
3. **Tree-size band assessment:** current `origin/main` tip has **112,740**
   files (`git ls-tree -r --name-only origin/main | wc -l`, this scan). The
   guard's band is ±0.15% of the base plus absolute floor/ceiling
   (90,000/150,000). 0.15% of 112,740 ≈ **169 files**. A 99-file deletion (net
   delta ≈ -99, plus whatever the optional cleanup in step 1 removes) is **well
   inside the ±169-file band** and inside the absolute floor — **no
   `--expect-files` override is needed** for the size-band check specifically.
   The other three checks (duplicate entries, `src/` entry band, load-bearing
   path floors) are structural, not count-based, and are unaffected by a
   same-directory-only deletion of this shape.
4. Push per `.claude/rules/vcs.md`: verify the outgoing range's diff only
   touches the intended paths, confirm off-target changed files = 0, then push
   and verify with `git ls-remote` + a post-fetch blob grep for
   `src/app/interpreter/` (expect it absent) and for the two edited specs
   (expect the new content present).

## 8. Measurement

- `origin/main` at time of scan: `78a24b4d143903f30f84a696f595c9947afd043b`.
- File inventory and all reference counts derived from `git ls-tree` /
  `git grep` against that commit object, not the working tree (I/O-saturated
  environment; working-tree `grep -r .` timed out with no output — see §2
  method note). No build, lint, or test run performed; no binary touched.

## 2026-08-17 re-verification — unchanged; awaiting the repo owner's decision

`git ls-files src/app/interpreter/ | wc -l` still returns **99**. Nothing about
the diagnosis has changed. This is not a defect a triage lane can close: the
deletion is a scoped, reviewed change that removes 99 tracked files, and the
prior doc explicitly reserves that decision for the repo owner. Deleting them
here would also collide with the `check-tree-size-push.shs` load-bearing-path
and file-count gates, which is exactly the review those gates exist to force.
Status OPEN, owner-gated, no code change.

## 2026-08-17 — executed

The recommendation was carried out. The uniqueness check this package listed as
NOT done was completed first and the tree was deleted; full evidence, counts and
the prevention guard are recorded in the companion doc,
`app_interpreter_tree_declared_removed_but_still_on_disk_2026-08-10.md`
(§ "2026-08-17 — RESOLVED").

Disposition of the two real inbound dependencies this package identified:
- `test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl`
  — repointed, not deleted. The two blocks that read the app-layer
  `watchdog.spl` now assert the property that outlives any single module: no
  app-layer copy exists to re-declare the externs, and the `WatchdogManager`
  facade still declares them. Strictly stronger than the old "this one file is
  clean". (One drafted assertion — that the isolation gate names `rt_watchdog` —
  was dropped after checking: `check-ui-backend-isolation.shs` bans app-layer
  externs by path class, not by symbol, so that assertion would have been false.)
- `test/03_system/feature/interpreter/runtime_error_stack_spec.spl` — repointed
  off the dead tree onto `bin/simple run`, and its fixture path corrected: it
  named `test/system/interpreter/sample/...`, which does not exist, so the spec
  had **never** passed — it failed on a missing file, not on its assertion. It is
  now left legitimately RED on the real assertion (the live path reports
  `error[E1002]` at semantic analysis, with no `Runtime error` header and no
  `Call stack:` section) and filed as
  `doc/08_tracking/bug/runtime_error_stack_absent_on_live_interpreter_2026-08-17.md`.
  Not weakened, not deleted, not marked pending.

# 364 of 413 check scripts are invoked by nothing

- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** high (verification is decorative at scale)
- **Measured at:** `a8da64469b41c084e78d1b2e509e72d925652159` (tree 109,569)
- **Date:** 2026-08-01

## Summary

A guard that no hook and no CI job runs is decoration. This repo has **413**
shell guard scripts under `scripts/check/`, `scripts/audit/`, and
`scripts/check-*.shs`. Under the most generous reachability model available,
**49 are invoked and 364 are not (88.1%)**.

The cause is structural, not incidental: the two places that list guards
(`.github/workflows/*.yml` and `scripts/hooks/pre-commit`) are **hand-maintained
lists**. Every new guard has to be remembered into them, and nothing detects the
omission. Adding a guard is easy; wiring it is a separate act nobody is forced
to perform.

## Method (reproducible)

Base commit `a8da6446`, `/usr/bin/grep` throughout (the default `grep` on this
host is ugrep and has silently disagreed on exclusion patterns).

1. Enumerate guards: tracked `scripts/{check,audit}/**.{shs,sh}` plus
   `scripts/check-*.shs` -> 413 scripts.
2. Build invocation edges `referrer -> guard-basename` two ways and take the
   UNION, so the orphan count is a conservative lower bound:
   - *narrow*: `sh|bash|source|exec <path>` and `./scripts/...` call syntax;
   - *broad*: any textual mention of the basename inside
     `scripts/ .github/ src/ bin/ tools/ config/`.
   The narrow model alone reports 383 orphans. It is wrong in the safe
   direction: it misses the `var="$repo_root/scripts/check/x.shs"` assignment
   form, which is exactly how the pre-push hook names its three sub-guards. The
   union model is the number reported here.
3. BFS from the real roots: all 27 `.github/workflows/*.yml`, `scripts/hooks/*`,
   and `scripts/check/pre-push-conflict-tree-guard.shs` (the script that
   `setup.shs` installs as `.git/hooks/pre-push`).

Counter-check on the method itself: the first run of this analysis reported
`INVOKED=0`, because the referrer field was read from `$2` of a `git grep`
line that has no commit prefix. A reachability audit that reaches nothing is
the same vacuity failure it exists to find; the field indexing was corrected
and the sanity assertion "at least one edge originates at a root" now holds
(13 such edges).

## Result

| Class | Count |
|---|---|
| Guards total | 413 |
| Invoked from a hook or CI (transitively) | 49 |
| **ORPHANED** | **364** |

Named guards checked by request:

| Script | Verdict | Evidence |
|---|---|---|
| `check-extern-registration.shs` | **ORPHANED** | zero referrers anywhere in the tree under either edge model |
| `check-seed-parse-superset.shs` | INVOKED | real `run:` step at `.github/workflows/rust-bootstrap-multiplatform.yml:178`; also listed in `scripts/hooks/pre-commit` (see caveat below) |
| `check-no-conflict-tree-push.shs` | INVOKED | via `pre-push-conflict-tree-guard.shs` |
| `check-no-conflict-markers-push.shs` | INVOKED | via `pre-push-conflict-tree-guard.shs` |
| `check-tree-size-push.shs` | INVOKED | via `pre-push-conflict-tree-guard.shs` |

The full orphan list is `scripts/check/guard_wiring_optout.txt`, landed with the
wiring change that follows this audit.

## Five distinct failure modes, not one

"Tracked but not invoked" is only the first axis. All five are live here:

1. **Orphaned** — the script exists, nothing invokes it. 364 scripts.
2. **Invoked but fail-open** — an earlier finding put ~70 of 92 audited scripts
   in this class. Where a script is *both* orphaned and fail-open it is pure
   decoration: it cannot run, and would report clean if it did.
3. **Hook on disk is a stale COPY of the tracked script.** PROVED this session:
   the shared repo's `.git/hooks/pre-push` was a 2,668-byte copy **two revisions
   behind**, predating `5f1b96ad9a8` — the commit that fixed three fail-opens in
   the conflict guards. Every hardening landed this session was absent from the
   hook that actually ran.
4. **Hook invokes only some of the guards it should.** The same pre-push hook
   previously ran only the conflict-*tree* guard, so literal conflict-*marker*
   text in file content was never checked on push.
5. **Hook is tracked, hand-listed, and installed by nothing.** PROVED:
   `git grep -E '(cp|ln|install)[^|;&]*scripts/hooks'` returns **zero** hits.
   Nothing installs `scripts/hooks/pre-commit`. The `.git/hooks/pre-commit`
   actually present in the shared repo is an untracked 2,488-byte secrets
   scanner dated Jun 23. So the five guards hand-listed in
   `scripts/hooks/pre-commit` — `check-workspace-root-guard`,
   `check-ui-backend-isolation`, `check-cpu-hotloop-idiom`,
   `check-seed-parse-superset`, `check-simpleos-native-surface` — **do not run
   at commit time at all**. Four of them are also in CI, so only
   `check-simpleos-native-surface.shs` is uniquely lost; but all five run
   post-push instead of pre-commit, which is not what their comments claim.

## Root cause of axis 3: the installer copies instead of linking

`scripts/setup/setup.shs` (still, at `a8da6446`):

    cp "${guard}" "${repo_root}/.git/hooks/pre-push.new"
    chmod +x "${repo_root}/.git/hooks/pre-push.new"
    mv "${repo_root}/.git/hooks/pre-push.new" "${repo_root}/.git/hooks/pre-push"

A copy is a snapshot. It goes stale the moment the tracked guard is improved,
and nothing reports the drift. The shared repo's hook was hand-replaced with a
symlink after the incident, but **the installer that created the hazard was not
fixed**, so the next `setup.shs` run re-creates it.

**Hooks must be symlinks, never copies.**

## What full enforcement would cost

Do not read "wire all 364" as the remedy. Most orphans are heavyweight evidence
producers — QEMU boots, GPU/Vulkan/DirectX readbacks, Electron and Bun browser
bitmap captures, FPGA and RISC-V hardware gates. They cannot run on a
general-purpose CI runner and were never meant to gate a commit. The defect is
not that they are unwired; it is that **nothing distinguishes "deliberately not
a gate" from "someone forgot"**. Those two states are currently
indistinguishable, which is why `check-extern-registration.shs` could land
hardened and gate nothing.

Specifically out of scope for the wiring change: `check-extern-registration.shs
--strict` exits 1 at ~2,377 unregistered symbols. It is wired **report-only**.
That backlog is a program needing an owner, not a lane's cleanup.

## Fix

Ratchet, matching the existing `ui_backend_isolation_baseline.txt` /
`cpu_lane_hotloop_baseline.txt` convention:

- `scripts/check/check-guard-wiring.shs` enumerates every guard, computes
  reachability from hooks and CI, and FAILS on any guard that is neither
  invoked nor listed in `scripts/check/guard_wiring_optout.txt` with a reason.
- The opt-out file is seeded with today's 364 orphans — an honest baseline, not
  an amnesty. Shrinking it is the follow-up program.
- The same script asserts every installed `.git/hooks/*` is a **symlink** into
  the tree (axis 3) and that its target is tracked.

Adding a guard now wires it automatically; *skipping* one becomes the deliberate
act that needs a written justification.

## Addendum: what the wiring change actually found

Wiring surfaced two live reds. Neither is weakened or allowlisted here.

**1. `check-ui-backend-isolation.shs` fails at HEAD.** Measured at `118ad7c2`
from the repo root:

    ui_backend_isolation_baselined=563
    ui_backend_isolation_current=545
    ui_backend_isolation_new=31
    ui_backend_isolation_ok=false      (exit 1, 49 stale baseline entries)

> **Follow-up (2026-08-01, same day):** triaged in
> `doc/08_tracking/bug/ui_backend_isolation_gate_red_and_unreachable_2026-08-01.md`.
> Three corrections to the paragraph below. (a) "CI-visible" was **wrong**: the
> step is step 5 of `code-idiom-gates` and step 4 fails on every push, so it
> reported `skipped` and had never executed — and `main` has no branch
> protection, so no conclusion gates anything. (b) The debt is older than HEAD:
> replaying the guard at `37cda4befdc` (2026-07-25) already gives `new=23`. (c) 7
> of the 31 were false positives from bare-token matching (comments, docstrings,
> error strings, and locals such as `val rt_nodes = ...`). After fixing the rule
> and pruning 105 stale baseline entries (563 → 458, none added), the gate stands
> at `new=24`, still exit 1. The pre-commit hook remains blocked, so the decision
> below not to install it was correct.

This guard is *already* wired into `.github/workflows/repo-hygiene.yml`, so the
debt is pre-existing and CI-visible. It is also hand-listed in
`scripts/hooks/pre-commit`. That is why this change does **not** make
`setup.shs` install the pre-commit hook: installing it today would fail every
commit in the repo on an unrelated pre-existing red. The blocker is recorded
rather than absorbed. Installing the pre-commit hook requires that ratchet to
be repaired first (31 new violations to fix, 49 stale baseline lines to prune);
the hook already chains a displaced `.git/hooks/pre-commit.local` so local
secret scanning survives the switch when it happens.

**2. `check-extern-registration.shs` is wired REPORT-ONLY.** `--strict` exits 1
at ~2,377 unregistered symbols. It runs without `--strict` in `repo-hygiene.yml`
so the count is printed on every run and can be driven down. Turning on
`--strict` is a program needing an owner. Do not add an allowlist and do not
lower its vacuity bound to shrink the number.

## Verification performed

Every claim below was observed end-to-end, not inferred from a script being
present in a list.

`check-guard-wiring.shs` — 6 source-level sabotages of its own selftest (BFS
neutered, orphan set forced empty, guard enumeration neutered, edge extraction
neutered, opt-out parsing neutered, reasonless-opt-out detection neutered): all
6 caught, unmodified control green. 4 behavioural sabotages against the real
tree: planted unwired guard -> `unwired_guard=`, exit 1; hook replaced by a copy
-> `hook_is_a_copy=`, exit 1; stale opt-out for a now-wired guard ->
`stale_optout_now_wired=`, exit 1; control -> `PASS — 413 guard(s) checked, 51
invoked, 362 orphaned (all justified)`, exit 0.

Push guards — verified through a REAL `git push` against a bare remote, driven
by the installed `.git/hooks/pre-push` symlink, not by running the scripts
directly:

| Fixture | Result | Remote ref |
|---|---|---|
| conflict-marker text in file content | **BLOCKED** by `check-no-conflict-markers-push.shs` (status 1), push exit 1 | unmoved at `a8da6446` |
| healthy commit | **PUSHED**, exit 0 | advanced to `2480a100` |

The marker fixture is the axis-4 case specifically: before `5f1b96ad9a8` the
pre-push hook ran only the conflict-*tree* guard, and the tree guard passes this
fixture. It is blocked now only because the hook runs both.

Hook install — `setup.shs`'s rewritten block was executed: it preserved a
pre-existing untracked `pre-commit` as `pre-commit.local` and installed
`pre-push` as a **symlink** (`ls -l` confirmed `lrwxrwxrwx`). The chained
`.local` hook was observed firing during a real `git commit`
(`LOCAL-HOOK-RAN` in the hook output).

## Remaining debt (not fixed here)

- **362 orphans** in `guard_wiring_optout.txt`. The set can no longer grow
  silently, but shrinking it needs an owner.
- **`scripts/hooks/pre-push` is shadowed.** Its tracking checks (`check-dbs`,
  `tracking check`, `traceability-check`) never run, because `.git/hooks/pre-push`
  is the conflict guard instead. Chaining them was not attempted: they require a
  built `bin/simple` and would block pushes on a fresh clone. This is a second
  live instance of axis 4.
- **`check-guard-wiring.shs`'s reachability model is textual**, so a guard
  merely *named* in a workflow comment counts as wired. It over-approximates
  reachability on purpose -- that under-reports orphans rather than failing a
  build on a parse gap -- but it means the 51 "invoked" figure is an upper bound.

## Orphan-shrinking pass 1 (2026-08-01, base `76c3e1e080d`)

Scope: the 141 opt-out entries carrying the placeholder reason "not yet
triaged". The other 221 (GPU / browser / QEMU / platform / perf) were left
alone -- their reasons are already substantive.

**First finding: the ratchet was already RED at `76c3e1e080d`.**
`check-guard-wiring.shs` exits 1 with `unwired_guard=check-lint-census.shs` --
a guard landed after the seeding and wired into nothing. The ratchet worked
exactly as designed; nobody had looked. Absorbed below.

### Wired (3) -- each fire-proved by sabotage, control green

| Guard | Protects | Fallout absorbed |
|---|---|---|
| `check-jit-runtime-symbol-manifest.shs` | silent whole-module de-JIT (~1000x) | 3 symbols added to `RUNTIME_SYMBOL_NAMES` |
| `check-spipe-submodule-gitlinks.shs` | index/tree shape corruption | none (green) |
| `check-lint-census.shs --self-test` | census scoring a crash as a checked file | none (green) |

`check-jit-runtime-symbol-manifest.shs` was red on `rt_array_at`, `rt_at` and
`rt_mem_attr_set_owner`. All three are emitted by codegen and defined with no
feature cfg (`value/collections.rs:648,683`, `value/heap.rs:675`) in
non-cfg-gated modules, so each was a silent de-JIT. They were **added to the
manifest**, not baselined. `rt_array_at`/`rt_at` back the `.at()` accessor.

Fire-proofs (all run from the worktree root, output to a file, file read):

- manifest guard -- control exit 0, `missing=0`, `manifest names: 1609`.
  Sabotage: drop `"rt_array_len"` **from `RUNTIME_SYMBOL_NAMES`** -> exit 1,
  names it. Drop `"rt_at"` (one this change added) -> exit 1, names both, which
  proves the added entries are load-bearing. Plant a quoted string inside a
  comment in the list -> exit 1, `PHANTOM manifest entries (1)`. Restore ->
  exit 0. *A first sabotage attempt did NOT fire*: the file holds two lists and
  the edit hit `CORE_REQUIRED_RUNTIME_SYMBOLS` instead. Recorded because a guard
  that "did not fire" is as often a bad sabotage as a bad guard.
- gitlink guard -- real fixture repo with a real submodule. Control exit 0,
  `PASS -- 2 path(s) checked`. Flatten the gitlink into a tracked file tree ->
  exit 1 `gitlink_bad ... mode=100644`. Collapse the tracked example tree to one
  entry -> exit 1 `tracked_tree_bad`. Restore -> exit 0. Also proved it works on
  a checkout with the submodule **not** initialised (`actions/checkout@v4`
  default): it reads `git ls-files --stage`, i.e. the index, not the worktree.
- lint-census self-test -- control `PASS: self-test 11 of 11`. Rewrite the
  classifier's `CRASH` verdict to `LINTED` at one site -> `FAIL: 4 of 11
  wrong`; at the other site -> `FAIL: 1 of 11 wrong`. Restore -> 11 of 11.

The guard contract was added to `check-spipe-submodule-gitlinks.shs`, which
previously printed only per-path lines: it now emits
`PASS -- <n> path(s) checked` and `ERROR -- nothing was checked` (exit 2).

All three steps carry `if: ${{ !cancelled() }}`, so a red earlier gate cannot
silently skip them -- the defect that left five gates unexecuted. YAML parsed
and the step list re-read after the edit; `code-idiom-gates` now has 11 steps.

Ratchet after the change: `PASS -- 414 guard(s) checked, 54 invoked, 360
orphaned (all justified)` (was 51 invoked / 362 orphaned, exit 1).

### Filed with a concrete count -- valuable, fallout beyond this lane

Every count below is from running the guard at HEAD from the repo root, exit
status read from a file, not a pipe.

| Guard | State | Count it would flag |
|---|---|---|
| `check-dangling-references.shs` | RED, exit 1 | **297 dangling references** -- imported names declared in no src file (`src/os/userlib/_Window/*` is a large cluster). Unresolved-symbol class; highest-value single item left. |
| `check-runtime-bundle-duplicate-symbols.shs` | ~~RED, exit 1~~ **GREEN, exit 0** (2026-08-01) | baselined 72, current 74, **new 2**: `rt_file_is_regular_no_follow`, `rt_is_interpreter_runtime`, each defined by both `runtime.c` and `runtime_native.c`. The guard's own text said *every native link will fail* -- **that consequence was INFERRED and is REFUTED at link level** (see "Link-level verdict" below). Guard wording corrected; both pairs triaged and baselined with reasons. Now 74/74/0. |
| `check-runtime-symbol-lane-divergence.shs` | ~~RED, exit 1~~ **GREEN, exit 0** (2026-08-01) | 907 symbols scanned, baselined 114, current 115, **new 1**: `rt_time_now_monotonic_ms` in `runtime_native.c` + `runtime_time.c`. **This one was REAL and severe** -- two different epochs behind one name. Fixed in `runtime_native.c`, then baselined with the reason. Now 115/115/0. |
| `check-core-lib-purity.shs` | RED, exit 1 | baselined 13, current 17, **new 5** (`font_registry.spl`, `js/engine/runtime.spl`, `renderdoc/backend_render_receipt_wire.spl`, `ui/widget_draw_ir.spl`, `ui/window_scene_draw_ir.spl`) **plus 1 stale baseline entry** (`ui/win_text_access.spl`). Tighten, never drop. |
| `check-api-arch-guard.shs` | RED, exit 1, 106s | 2 arch-doc hash mismatches (`00_compiler_architecture.md`, `mcp_performance_regression_enforcement.md`) + module-symbol drift. Baseline is doc-hash based and needs `--update-baseline` by an owner. |
| `check-type-name-collisions.shs` | exit **0**, warn-only | **85 colliding names** (e.g. `HandshakeResult` declared as both enum and struct). Exits 0 by design, so wiring it as-is gates nothing -- it must be promoted to fail-on-new-collision first. |

### Reclassified -- the reason was wrong, not the guard

- `check-lint-rejects-unparseable.shs` -- green (16s) and it guards a real blind
  spot (`simple lint` not failing closed on an unparseable file), but it needs a
  **built `bin/simple`**. It cannot go in `code-idiom-gates`, which only checks
  out. Belongs in a workflow that builds the compiler.
- `check-keyword-identifier-bindings.shs` -- green, pure git+grep, `cd`s to its
  own repo root so it cannot fail open on cwd. Blocked on the contract only: it
  prints a bare `OK: no keyword bindings` with **no count**. Needs a count first.
- `check-heavy-work-preflight.shs` -- not a gate at all. It measures live machine
  state (swap, 1m load, dirty-file count: 8046 here) and reports `BLOCKED`. It is
  an operator preflight; the placeholder reason should say so.
- `check-sspec-count-truthful.shs` -- takes spec paths as arguments and exits 2
  with a usage message when given none. Needs a driver that supplies targets.
- `check-req-traceability.shs` -- lives at `scripts/check/cert/`, not
  `scripts/check/`. Basename-keyed opt-out entries hide that.
- `check-compiler-provenance.shs` -- green (47s) but informational: it prints
  which fix commits are present in the deployed binary and says so itself
  ("Symbol presence alone does not prove reachability").

Orphans remaining: **360**, of which **127** still carry the placeholder reason
(down from 141: 2 were wired and 12 placeholder reasons were replaced with a
substantive one, so "deliberately not a gate" is now distinguishable from
"someone forgot" for those).

## Link-level verdict on "every native link will fail" (2026-08-01) -- REFUTED

Base sha `9349ff90f60fbce062d9a5c321df9ed51cd9b4fd`, origin-tip worktree, real
`clang-18` + `ld.lld-18`. The static fact (each of
`rt_file_is_regular_no_follow` / `rt_is_interpreter_runtime` defined once in
`src/runtime/runtime.c` and once in `src/runtime/runtime_native.c`) is
confirmed. The **consequence** was inferred from file contents and is wrong.

### PROVED

1. `runtime.o` and `runtime_native.o` already share **23 strong (`T`) symbols**
   at this sha -- `rt_dir_create`, `rt_fd_write`, `rt_fd_read_until`,
   `rt_fd_close`, `rt_text_to_bytes`, the `rt_bdd_*` family, and others. The two
   new symbols join a large pre-existing family, they do not create one.
2. `ld.lld-18` linking just those two objects **without** muldefs reports
   **20 duplicate-symbol errors** -- so if the build linked them naively, it
   would have been failing on 20 other symbols long before these two.
3. `llvm_native_link.spl` passes `allow_duplicate_definitions: not
   stage4_requested` (line ~1579), i.e. `-z muldefs` /
   `--allow-multiple-definition` on the default profile. Linking the **full
   14-object bundle** from `runtime_compiler.spl`'s `sources` array with that
   flag: `rc=0`, `0` duplicate errors, `0` undefined symbols, output is a real
   `ELF 64-bit LSB pie executable`, `nm` shows all three symbols at real
   addresses (`T rt_file_is_regular_no_follow` @ `0x197c0`,
   `T rt_is_interpreter_runtime` @ `0x16290`,
   `T rt_time_now_monotonic_ms` @ `0x34b50`), and **running it** prints
   `is_regular(/etc/hostname)=1 / is_interp=0 / mono_ms_positive=1`, exit 0.
4. `runtime` (i.e. `runtime.c`) is **not** one of the stage4 `candidate_labels`
   (`compiler_backfill, runtime_native, runtime_legacy_compat, runtime_process,
   runtime_dynload, runtime_font, runtime_memtrack, runtime_timestamp`), so a
   `runtime.c` / `runtime_native.c` pair never reaches a stage4 archive core.
5. The Rust driver's own native link (`build_c_runtime_library` in
   `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`) compiles
   `runtime_native.c` and **not** `runtime.c` -- mutually exclusive there.
6. The guard's own numbers refute it: **72 duplicate pairs were already
   baselined** in this same bundle, 31 of them `runtime.c,runtime_native.c`.

**Verdict: not a live breakage.** Native links work today and would have kept
working. The 2026-07-24 regression the guard's header cites was real but was
specific to the **stage4 strict** profile.

### Still worth fixing (and fixed)

Both pairs are deliberate per-lane definitions -- lane C
(`src/app/compile/native.spl` `rt_sources`) compiles `runtime.c` without
`runtime_native.c`; lane B (`native_project/tools.rs`) compiles
`runtime_native.c` without `runtime.c` -- so neither copy can be deleted.
Bodies were compared and are byte-identical (`rt_file_is_regular_no_follow`) /
both `return false;` (`rt_is_interpreter_runtime`, and the `runtime_native.c`
copy is inside `#if defined(SIMPLE_CORE_C_STANDALONE)`). Baselined with those
reasons. The guard's failure message was rewritten to state the real
consequence per link profile -- **first-definition-wins under muldefs, so
behavioral drift becomes a silent wrong answer, not a build error** -- instead
of the false "every native link will fail". Threshold unchanged (0 new fails).

## `rt_time_now_monotonic_ms` -- GENUINE divergence, FIXED

Not the same story. Two lanes, **two different epochs behind one public name**:

| lane | source | reading at startup |
|---|---|---|
| A (Rust-seed cdylib) | `src/runtime/runtime_time.c` | `0` (ms since process start) |
| B (core-c bootstrap) | `src/runtime/runtime_native.c` | `22255054` (ms since **boot**; box uptime `22255060`) |
| interp | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` | `0` (ms since process start, `Instant` baseline) |

PROVED by compiling each lane's source set and **running two real linked ELF
binaries**, not by reading source. `runtime_native.c` was the outlier, 2 of 3
lanes agreed on process-relative, and its own sibling doc comment in
`file_io.rs` documents the process-start contract.

All current in-tree callers (`src/lib/nogc_sync_mut/diag.spl`,
`src/lib/nogc_sync_mut/src/core/decorators.spl`,
`src/compiler/80.driver/driver_log_helpers.spl`,
`src/lib/nogc_sync_mut/io/browser_net_runtime.spl`) use the value as a
**delta**, so the divergence was latent rather than actively corrupting -- but
any caller reading it as "elapsed since process start" (what the name and the
other two lanes promise) was silently wrong on lane B only.

Fixed in `src/runtime/runtime_native.c` by capturing a process-start baseline.
Verified by relinking and running: reading is now `0` at startup on both lanes,
and a 120 ms `nanosleep` still yields `delta=120`, so monotonic-delta semantics
are preserved. `rt_time_now_ns` / `rt_time_now_nanos` / `rt_time_now_micros`
were deliberately left absolute -- they are separately baselined and owned by
another lane.

## `check-dangling-references.shs`: 297 -> 171 (2026-08-01)

### The static count IS the defect count -- corroborated two ways

Before touching anything, the 297 findings were cross-checked against an
**independently written** definition index (its own regex over `fn`/`me`/`val`/
`var`/`const`/`struct`/`class`/`enum`/`trait`/`mixin`/`type`/`actor`/
`extern fn`/`literal`, plus enum-variant and struct-field bodies, plus
`export use ... as` aliases). Result: **297 findings, 297 confirmed undeclared,
0 disagreements.** The guard is not over-reporting here.

Runtime oracle on a representative, seed binary, `SIMPLE_EXECUTION_MODE=interpreter`:

| probe | result |
|---|---|
| `use std.gc_async_mut.opencl.{opencl_available}` then `print "ok"` | rc=0, prints `ok` |
| same import, then **call** `opencl_available()` | rc=1, `error[E1002]: function 'opencl_available' not found` |

So the **module loader is fail-open on unresolved imports** -- a dangling import
binds nothing and costs nothing until the name is actually called, at which
point it is a hard error. That is exactly why the two incidents this guard was
written for only surfaced at full bootstrap, and it means every one of these is
a live landmine rather than dead weight.

Note: **none** of the 297 pointed at the deleted `30.types/type_system`
inference cluster or the `.spipe_matchers_*` artifacts (`grep -c` = 0 for both).
That expectation did not hold; these are unrelated pre-existing debt.

### Batch 1 -- case (b), target module exists nowhere and the facade is unused

`src/lib/gc_async_mut/opencl.spl` and `src/lib/gc_async_mut/opencl/__init__.spl`
were each nothing but a single `export use std.nogc_sync_mut.opencl.mod.{...}`
of 19 names. `src/lib/nogc_sync_mut/opencl` does not exist, no file anywhere
defines `opencl_available` or any sibling, and a tree-wide search found **zero**
importers of either facade. Both files deleted. **-38 findings** (297 -> 259).

### Batch 2 -- case (b), dangling import names the importing file never uses

For each remaining SYMBOL finding, checked whether the name appears anywhere in
its own file **outside** the `use` statements (multi-line braced `use` blocks
tracked properly). A name that is declared nowhere AND read nowhere binds
nothing and is read by nothing, so removing it cannot change behavior.

**88 names removed across 33 files** (259 -> 171). 111 SYMBOL findings were
**kept** because the file really does use the name -- those are case (a)/(c) and
need a decision, not a deletion. Structural check on all 33: brace counts
unchanged, no empty or malformed import lists introduced (the 4 trailing-comma
lists flagged were pre-existing style, verified against `HEAD:<file>`).

### Remaining: 171 = 48 MODULE + 111 SYMBOL + 12 METHOD

Not silently absorbed. Split by whether the target module exists at all:

**A. Module exists nowhere -- 96 findings / 28 clusters.** Whole import lines
are pointed at modules that were never written or were deleted with their
callers left behind. Largest: `std.async_core` (12 findings across 12 files),
`std.common.unicode.codepoint` (9), `app.build.quality` (6),
`std.math.bignum.bignat` (5), `common.display_protocol.display_protocol` (5),
`host.common.io.fs_ffi` (4), `std.common.math.field.fe_p256` (4). Plus 12
METHOD findings (`self.foo(...)` with no `fn foo`/`me foo` anywhere) across 7
files -- same class as incident 1, the one that broke the bootstrap.

**B. Module exists, the symbol does not -- 75 findings / 34 clusters.** These
are the case-(a)/(c) split and need per-symbol judgement. Largest:
`app.dashboard.main` (16 across 2 files), `common.window_protocol.window_protocol`
(7 across 4 files -- `WM_STATUS_OK`, `WM_STATUS_ERROR`, `WM_EVENT_FOCUS`,
`wm_input_event` are genuinely called; the module declares only 7 names and
these are not among them, so this is case (c) "implement it": the request types
exist without their response/status/event-kind counterparts),
`std.{gc,nogc}_async_mut.js.engine.interpreter` (4 each),
`compiler.tools.leak_check.types` (3), `host.common.io.types` (3).

These 171 are a program with an owner, not a lane cleanup: each one is either a
rename to chase or a missing implementation to write, and several sit in
subsystems (`os/compositor`, `os/services/netstack`, `ui.*`, `app.dashboard`)
that other lanes are live in. Filed here with exact counts so the next pass
starts from a number rather than a re-scan.

## Lane J re-verification 2026-08-17 (classified by CONTENT, not SHA ancestry)

**Verdict: STILL-OPEN (census).** Duplicate-family with
`check_guard_wiring_48_unwired_triage_2026-08-08.md`. The optout list landed but the orphan
count itself was never reduced. Not reduced by this lane either.

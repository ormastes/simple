# `env_get(...) ?? default` is a DEAD fallback against `std.io_runtime`'s `env_get` — silently yields `""` instead of the default

- **ID:** env_get_nil_coalesce_dead_fallback_2026-07-25
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Severity:** high — silent wrong value, no error, no warning; the idiom reads
  as correct and is used ~680 times in-tree.

## The defect

`env_get` exists with **two different return types**:

| definition | returns |
|---|---|
| `src/lib/nogc_sync_mut/io_runtime.spl:174` (`std.io_runtime`) | **`text`** |
| `src/lib/nogc_sync_mut/env/variables.spl:11` | **`text`** |
| `src/lib/nogc_sync_mut/src/config.spl:764` | **`text?`** |

`??` (nil-coalesce) only fires on `nil`. A plain `text` is never `nil` — an unset
variable comes back as `""`. So against the first two definitions:

```
val x = env_get("UNSET_VAR") ?? "fallback"      # x == ""   NOT "fallback"
```

Verified by probe on the session-built full CLI:

```
is nil?      : false
?? fallback  : []          <-- empty, fallback never taken
```

The idiom looks correct because a **sibling `env_get` really does** return
`text?`, where `??` is the right thing. Which one you get depends on your import.

## How it surfaced

`widget × host-WM` showcase cell reported `status=fail reason=ppm-write-failed`
with the default path, but passed when `SIMPLE_WM_HEADLESS_CAPTURE_PPM` was set.
The write was never the problem:

```
wm_widget_showcase_host_headless_failed_ppm_path=          <-- EMPTY
wm_widget_showcase_host_headless_failed_ppm_bytes=1663215  <-- payload fine
```

`ppm_path` was `""`, because
`env_get("SIMPLE_WM_HEADLESS_CAPTURE_PPM") ?? path_join(...)` never reached the
`path_join`. Hours went into ruling out permissions, directory existence, payload
size, filename collisions and `path_join` correctness — all of which were fine —
because the failure was reported as a *write* failure and the path was not
printed. (That diagnostic gap is now fixed; see "Fixed" below.)

## Fixed

- `examples/06_io/ui/wm_widget_showcase_gui.spl` — the `ppm_path` site now uses
  an explicit `!= ""` check instead of `??`, with a comment explaining why.
- Same file: the failure branch now prints `failed_ppm_path` /
  `failed_ppm_bytes`, and `dir_create_all`'s ignored return is checked and
  reported as a distinct `tmp-root-create-failed` reason. Without these two the
  root cause stays invisible.

## NOT fixed — the general case

`grep -rn 'env_get([^)]*) *??' --include=*.spl src examples` → **680 occurrences.**

**That is 680 occurrences, not 680 bugs.** A site is only broken if the
`env_get` in scope is a `text`-returning one. Sites importing the `text?`
variant are correct. Each occurrence must be checked against its own import
before being touched — a blind sweep would be wrong.

Highest-count files (import not yet verified per-file):

| count | file |
|---|---|
| 22 | `examples/06_io/ui/widget_showcase_gui.spl` |
| 17 | `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` |
| 14 | `src/app/io/_CliCompile/compile_targets.spl` |
| 9 | `examples/06_io/ui/wm_web_standards_showcase_gui.spl` |
| 9 | `examples/06_io/ui/wm_graphics_2d_showcase_gui.spl` |
| 9 | `examples/06_io/ui/graphics_2d_showcase_gui.spl` |
| 8 | `examples/06_io/ui/wm_widget_showcase_gui.spl` (1 of 8 fixed) |
| 8 | `src/app/ui.web/server.spl` |

Note the two other host-WM showcase wrappers (2D, web) each carry 9 — the cells
I have not yet run. Expect the same class of failure there.

## Recommended real fix (pick one, do it deliberately)

1. **Unify `env_get` on `text?`** and let `??` mean what every call site already
   assumes. Most correct; touches every `text`-returning call site.
2. **Rename** so the two cannot be confused (`env_get` -> `text?`,
   `env_get_or_empty` -> `text`). Makes the wrong idiom impossible to write by
   accident.
3. At minimum, make the compiler **warn on `??` applied to a non-optional**
   expression — it is provably dead code and would have caught all 680 sites,
   plus the four other same-name-collision defects found the same day.

Option 3 is the same lever as "make same-name collisions loud at registration"
(`doc/03_plan/ui/showcase_matrix_replan_2026-07-25.md` P5): a diagnostic that
turns a silent whole class into a build-time error.

## Related — fifth same-name divergence found 2026-07-25

`ant-trace`/`ant_trace`, `CompiledSymbolKind`, `Engine2D` across tiers,
`MouseEvent` (ps2_mouse vs input_event), and now `env_get` (`text` vs `text?`).
Same root habit: one name, several definitions, silently diverged.

---

## 2026-08-08 sweep — a THIRD contract shape, and the silent-abort half

The 2026-07-25 table above lists two shapes (`text` and `text?`). Measurement on
the deployed `bin/release/x86_64-unknown-linux-gnu/simple` shows there are
**three**, and the missing one is where the damage is:

| shape | behaviour for an UNSET var | `?? default` | `.method()` |
|---|---|---|---|
| **A. `-> text`, nil-GUARDED** | `""` | **DEAD** (yields `""`) — the 07-25 bug | safe |
| **B. `-> text`, UNGUARDED passthrough** | **`nil`** | **works** | **ABORTS the enclosing fn** |
| **C. honest `text?`** | `nil` | works | aborts unless unwrapped |

Shape B is `fn env_get(key: text) -> text: rt_env_get(key)` — the declaration
lies, and the interpreter does not enforce it. A and B are indistinguishable at
a call site; which one you get depends purely on your `use` line.

### The silent-abort half (this is the dangerous part)

Calling a text method on a shape-B result aborts the **whole enclosing
function** — it never reaches ANY return. Sometimes with
`semantic: method 'trim' not found on type 'nil'`, and sometimes — measured
2026-08-08 — with **no diagnostic at all**: the call expression just evaluates
empty and execution continues. An aborted function and a correct one are
therefore indistinguishable from outside. This is the same mechanism root-caused
for `credential_kdf_cost` in `282cda42f`.

### Enumeration (unbounded; `/usr/bin/grep`, not the .gitignore-honouring wrapper)

17 `fn env_get(key)` definitions. **Guarded (A):** `io_runtime.spl:177`,
`nogc_sync_mut/env/variables.spl:11`, `nogc_async_mut/env/variables.spl:11`.
**Honest (C):** `nogc_sync_mut/src/config.spl:764`,
`gc_async_mut/env/variables.spl:8`. **Unguarded (B), 8:**
`compiler/00.common/config.spl:8`, `compiler/80.driver/build_log.spl:22`,
`compiler/90.tools/header_gen/shared_lib_flags.spl:16`,
`nogc_sync_mut/ffi/system.spl:26`, `nogc_sync_mut/io/mod_stub.spl:46`,
`nogc_sync_mut/io/env_ops.spl:36`, `nogc_sync_mut/sffi/system.spl:26`,
`nogc_async_mut/io/mod_stub.spl:72`, plus `os/port/llvm/build.spl:25`.

`env_ops.spl` is the widest blast radius — 20+ importers across compiler, CLI
and test-runner.

### Call-site family: 15 grep hits, 13 already safe, 2 genuinely broken

`env_get\([^()]*\)\.[a-z_]` returns 15 sites. Resolving each `use` line to its
definition:

- **10 safe** — `src/app/ui_showcase/hosts/{main_2d,main_gui,main_wm,main_web,host_wm}.spl`
  all import `std.io_runtime.env_get`, which **guards** (shape A). Measured
  `REACHED_wrapper=[]`. *The 15-site figure was a false family.*
- **2 safe** — `nogc_sync_mut/env/platform.spl:93,105` import
  `std.env.variables.env_get` (shape A).
- **1 safe** — `compiler/70.backend/backend/runtime_compiler.spl:54` already
  checks `!= nil` explicitly.
- **2 BROKEN** — `nogc_sync_mut/test_runner/test_runner_async.spl:52,56`
  (`_get_temp_dir`) import shape-B `io.env_ops.env_get`. **FIXED 2026-08-08.**

`_get_temp_dir` aborted before any return whenever `TMPDIR` was unset — the
DEFAULT state of a stock Linux shell — so every temp-file creation in the async
test runner died silently. Guarded with the `?? ""` idiom (the codebase's
dominant form, 282 sites).

Note the chain-grep cannot see two-step usage (`val v = env_get(K)` then
`v.trim()` on a later line); the counts above are a lower bound.

### Why the ROOT was NOT changed — and this is the key constraint

Making shape B return `""` (or fixing `rt_env_get`) looks like the right root
fix and is **not safe**: **22 of 36 pattern-matched call sites are VERIFIED leak-dependent** and would
silently regress to `""` — e.g. `env_get("SIMPLE_BINARY") ?? "bin/simple"`,
`env_get("CLAUDE_BASE_API_URL") ?? "https://api.anthropic.com"`,
`env_get("PWD") ?? "."`. Guarding the wrapper silently turns all 36 into `""`.

So the two halves of this bug pull in **opposite directions**: the 07-25 half
wants shape B everywhere (so `??` lives), the abort half wants shape A
everywhere (so `.method()` is safe). Neither can be applied globally. That is
why option 2 above (**rename so the two shapes cannot be confused**) is the only
fix that resolves both, and it remains the recommendation.

Until then: fix the reachable abort sites individually with `?? ""`, and treat
any `env_get(...) ?? "non-empty"` as suspect until its `use` line is resolved.

### Positive control

`scripts/check/check-env-get-nil-abort-guard.shs` — 5 assertions, exit 0 = safe.
Because the failure is a SILENT abort, it asserts the probe function **reached
its return** via a `REACHED_` marker emitted on the line *after* the method call
(an abort cannot forge it), and it asserts the unguarded form still **does**
abort, so the control cannot go vacuous. Verified RED when the fix is reverted
(2 of 5 fail), GREEN when restored.

Edit-visibility for every measurement above was proven by injecting a
`SABOTAGE_MARKER_Q7` into `io_runtime.spl`'s guard and observing it in probe
output (then reverting; blob restored to `f47b2a2715d0`) — ruling out the
bundled-stdlib trap.

### 2026-08-08 addendum — the 36 figure resolved by import (corrects the above)

The "36 sites" above was first obtained by **text pattern only**
(`env_get(...) ?? "non-empty"`), without resolving each `use` line. Resolving
them the same way the 15 chain sites were resolved splits the 36 three ways —
and the split matters, because roughly a third are not leak-dependent at all but
are **already-broken instances of the 07-25 dead-fallback half of this very
bug**:

| sites | resolves to | shape | status |
|---|---|---|---|
| 20 | `app.io.mod` → re-exports `std.nogc_sync_mut.io.env_ops.env_get` | B unguarded | **leak-dependent** — guarding the wrapper WOULD regress these |
| 2 | `std.nogc_sync_mut.io.env_ops.env_get` (direct) | B unguarded | **leak-dependent** |
| 10 | `std.io_runtime.env_get` | A **guarded** | **ALREADY BROKEN** — `??` is a DEAD fallback here, silently yielding `""` instead of the stated default |
| 4 | module-local / wildcard | mixed (`src/config.spl` is honest shape C) | correct or n/a |

So the accurate statement is **22 of 36 verified leak-dependent**, not 36. The
decision not to change the root still stands on those 22 — but the figure in the
commit message for the `_get_temp_dir` fix (`f889cf1d`) says 36 and should be
read as 22.

The 10 dead-fallback sites are NEW, previously uncounted instances of the
07-25 defect and are still OPEN:

- `src/app/mcp/startup_log.spl` (3)
- `src/app/simple_lsp_mcp/startup_log.spl` (3)
- `src/app/ui.web/server.spl` (2)
- `src/app/game.rollball/game.spl` (2)

Each reads as if it applies a non-empty default and in fact yields `""`. They
need `env_get_or(key, default)` (or an explicit `if x == ""` test), not `??`.

Method note: resolve the `use` line before classifying ANY `env_get` site. A
pattern count across `env_get` is meaningless on its own, because the same
spelling resolves to three different contracts.

## 2026-08-17 — correction to commit 18f7724's claim

Commit `18f7724` states "Both specs verified with a real negative control".
**That is inaccurate and is corrected here.** Only the REPRODUCING spec was
executed:

```
fix in place    -> Results: 5 total, 5 passed, 0 failed    rc=0
defect restored -> Results: 5 total, 3 passed, 2 failed    rc=1
```

The 5 examples are all from `env_get_nil_coalesce_fallback_spec.spl`. The
defect was restored by mutating `env_get_opt` to return `""` instead of nil,
which proves that spec non-vacuous.

`env_nullable_lookup_family_detection_spec.spl` — the class-detection half —
has **never produced a `Results:` line**, across five attempts (two via
`test-slot.shs`, three direct). Every run was terminated during the ~310s
session-setup phase, leaving only `[gc-warning]` noise and no test header.
It is therefore **UNVERIFIED and possibly vacuous**, and must not be counted
as coverage until someone quotes its verdict on a quieter host.

The fix itself is unaffected: it rests on the reproducing spec's
before/after pair plus the direct `bin/simple run` probe. Only the claim about
the second spec was too strong.

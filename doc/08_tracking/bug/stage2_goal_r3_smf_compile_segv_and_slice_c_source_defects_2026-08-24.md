# stage2 goal-r3 `compile --format=smf` SEGVs on 2-line fixtures; slice-C source defects found underneath it

- **Date:** 2026-08-24
- **Lane:** R (slice C — `src/app/mcp`, `src/app/cli`, `src/compiler/{80.driver,90.tools,99.loader}`)
- **Compiler under test:** `build/bootstrap/goal-r3/stage2/x86_64-unknown-linux-gnu/simple`
  (132,945,096 bytes, mtime 2026-08-24 02:50)
- **Worktree:** `/mnt/data/worktrees/goal-lane-r-build-C` at `826d7aa20c4` (clean, == committed `main`)
- **Status:** compiler defects OPEN (not this lane's tree); source defects PARTIALLY FIXED

## 1. Headline

`simple compile <file> --format=smf -o <out>` **SIGSEGVs (rc 139) on two-line
source files**. The crash is deterministic (3/3 reruns on the same fixture) and
reproduces with no imports, no stdlib use, and a one-module closure. It is not a
memory-pressure artifact: it fires in under a second at 108 GB free.

This dominates the sweep. Of the first 58 slice-C files compiled, **42 crashed**
(9 during HIR lowering, 33 after `post-diagnostics`), and the crash rate is a
property of the binary, not of the source.

The `error: hir codec: no \`Visibility\` arm for tag -1` line the task brief
names as a known constant turns out to be the *lucky* outcome: files that reach
it exit rc 1, and files that do not reach it SEGV at the same stage. **The
known-constant filter therefore cannot be text-based.** The usable signal is
positional: the `[bootstrap-error-count] ... point=post-lowering / post-diagnostics
count=N` lines are printed *before* either failure, so a crashed run still
carries a verdict for everything up to that point.

## 2. Compiler defect fixture table

All fixtures compiled with `timeout 120 <stage2> compile X.spl --format=smf -o /tmp/fx.smf`.
Exit status read directly into a variable on the line after the invocation.
Fixtures live in the sweep scratchpad (`fx/`); each is reproduced verbatim below.

| # | source | rc | last stage marker reached |
|---|--------|----|---------------------------|
| C-1 | `fn f():`<br>`    val x = 1` | **139** | `[build] hir 0/1` — crash *inside* HIR lowering, no `post-lowering` line |
| C-2 | `extern fn print_raw(s: text)` (whole file) | **139** | `[build] hir 0/1` — same shape |
| C-3 | `fn f(x: i64):`<br>`    return` | **139** | `[build] hir 0/1` |
| C-4 | `fn f() -> i64:`<br>`    return 1` | **139** | `[cranelift-direct] module` — reached `post-store count=0`, crashed later |
| C-5 | `fn f() -> i64:`<br>`    1` | 1 | `error: ... MIR lowering error: E-SFFI-016: missing return in non-unit function 'f'` |
| C-6 | `fn f(b: text) -> text:`<br>`    b + "x"` | 1 | same E-SFFI-016 |

**Three distinct classes, not one law.** Do not read C-1..C-3 as "any `return`
crashes" — plenty of real slice files that are full of `return` statements
reached `post-diagnostics count=0` cleanly. The fixtures are recorded as
observations for the compiler owners to unify; root-causing them is outside this
lane's slice.

**C-5/C-6 (E-SFFI-016) is a separate, milder defect:** implicit tail-expression
return is pervasive, idiomatic Simple, and MIR lowering rejects it as "missing
return". It fired only **once** across the whole real-source sweep (a
`bootstrap_version` function in `src/app/cli`), because real code mostly uses
explicit `return` — so it is a low-frequency defect, recorded rather than
prioritised.

## 3. Slice-C source defects found (real, not compiler artifacts)

Detected via `[hir-fatal]` / `point=post-diagnostics count=N` with N > 0, all of
which print before any crash.

### 3.1 FIXED — cast to a non-existent type (`as int`)

`src/app/mcp/debug_eval.spl:14` and `src/app/mcp/debug_session.spl:59` cast with
`as int`. `int` is not a Simple type; HIR lowering reports `unresolved type: int`.
Fixed to `as i64`.

Empirical boundary, measured against the compiler on 2026-08-24 with a single
fixture casting to six names: **`int`, `long`, `double`, `uint` are rejected**
(`unresolved type: <name>`); **`float` and `str` resolve fine**. The lint rule
below flags exactly the four rejected names, so it cannot false-positive.

Repo-wide population of the class: **148** sites (`src/**/*.spl`).

### 3.2 FIXED — `for x in range(a, b):`

`range` is not a resolvable global in the self-hosted compiler. The only
function definition is `gc_async_mut.pure.collections.range` and **no file in
the tree imports it**; everything else named `range` is a container *method*.
So `for _i in range(0, n):` fails with `unresolved name: range`.

Fixed to the range-expression form `for _i in 0..n:` at 6 sites in
`src/app/mcp/debug_eval.spl` and 1 in `src/app/mcp/debug_log_tools.spl`.

Repo-wide population of the class: **340** `for ... in range(` sites.

### 3.3 NOT FIXED — dead MCP modules importing modules that do not exist

`src/app/mcp/{completions,debug_log_tools,debug_handlers}.spl` `use`
`app.mcp.helpers`, `app.mcp.resources`, `app.mcp.prompts`, `app.mcp.log_store` —
**none of which exist**; `src/app/mcp/` has 36 entries and none of those four.
None of these files is in `src/app/mcp/main.spl`'s 61-module closure, so they are
orphaned.

**Detection already exists and already sees them.** `scripts/check/check-use-target-resolves.shs`
classifies them `MODULE_MISSING` and they are already recorded in
`scripts/check/use_target_resolves_baseline.txt` at lines 86397-86403. That
baseline holds 110,389 rows (MEMBER_NOT_VISIBLE 68953, UNRESOLVABLE 20134,
MEMBER_MISSING 17264, MODULE_MISSING 4038). No new detection layer is warranted
here; the debt is tracked. Deleting the files is deliberately **not** done —
proving nothing depends on them is a separate piece of work, and the house rule
forbids deleting on a hunch.

## 4. Detection layer chosen

Per the standing principle — compiler first, then lint, then a `scripts/check/` gate:

| defect | layer | why |
|--------|-------|-----|
| `as int` (3.1) | **lint** (`TYPE001`) | The compiler already errors, but only after lowering a whole module closure — minutes. A line scan finds it in milliseconds, and the rejected-name set is empirically closed so the rule is exact. |
| `for ... in range(` (3.2) | **lint** (`TYPE002`) | Same argument. Scoped to the `for ... in range(` shape on purpose: a bare `range(` also matches legitimate `vec.range(...)` methods, which must not be flagged. |
| missing modules (3.3) | existing `scripts/check/check-use-target-resolves.shs` | Already owns module/member resolution and already lists these rows. Adding an overlapping lint would be scope creep. |
| SEGV / E-SFFI-016 (2) | compiler, not this lane | Recorded here as a fixture table; the binary has a rebuild pending. |

### The rule

- `src/compiler/90.tools/lint/_LintMain/nonexistent_type_lints.spl` (new)
- wired in `lint_checks.spl` (`check_nonexistent_types`, dispatched alongside
  `check_accessor_and_parent_names`), `config_and_model.spl` (config family
  `nonexistent_type`), and re-exported from `lint/main.spl`.
- **Warn, not deny**, deliberately: the tree already carries 148 + 340
  pre-existing sites, and a new deny would red every lane at once. Promotion to
  deny is the correct end state and is gated on that population reaching zero.
  Do not weaken or delete the rule instead of doing that work.

### Reproduce spec

`test/01_unit/compiler/lint_nonexistent_type_rules_spec.spl` — 13 examples,
including the exact pre-fix and post-fix `debug_eval.spl` shapes as regression
fixtures.

- **Before the lint change** (`git stash push -- src/compiler/90.tools/lint/`):
  `outcome=ERROR declared>=13 executed=13 passed=0 failed=13`, rc 1.
- **After:** `outcome=OK declared>=13 executed=13 passed=13 failed=0`, rc 0.

Run with the Rust seed (`/mnt/data/worktrees/simple-main/bin/simple test`): the
goal-r3 stage2 binary is the BOOTSTRAP cli and has no `test` subcommand.

## 5. Verification bar — stated honestly

The maximum provable verdict under this binary is **`post-diagnostics count=0`**
— source is sound through HIR lowering and diagnostics. MIR, codegen and the SMF
codec are unverifiable, because the binary crashes or errors there on trivial
input. `debug_eval.spl` and `debug_session.spl` are fixed **to that bar** and no
further. Nothing in this record should be read as "compiles clean".

Coverage caveat: a run that crashed *after* `post-diagnostics` still verified its
root file. A run that crashed *during* HIR lowering (class LOWERING-CRASH,
including `src/app/mcp/main.spl`) verified **nothing** — those files are UNKNOWN,
not clean.

## 6. Artifacts

Sweep driver, per-file logs, and classifier live in the session scratchpad
(`.../scratchpad/laneR/{run.shs,classify.shs,logs/,results.tsv,class.tsv,fx/}`).
Per-file logs are the before-fix evidence for §3.1 and §3.2.

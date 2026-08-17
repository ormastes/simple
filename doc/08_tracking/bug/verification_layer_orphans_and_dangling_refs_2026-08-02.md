# Verification layer: orphaned guards and dangling references, re-derived

- **Status:** open (two backlogs, both owned below)
- **Measured at:** `66974acc79e754d202c53881eeac08fd86a2a8db`, tree 109,671
- **Date:** 2026-08-02
- **Tooling:** `/usr/bin/grep` pinned throughout (`grep` on this host is ugrep).

This re-derives two counts that were previously INFERRED from a sweep, states
the predicate used for each, and records what was repaired. Every number below
was produced by running the guard, not by estimating.

## Backlog 1 — orphaned guards

**Predicate.** A guard is `scripts/{check,audit}/**.{shs,sh}` plus
`scripts/check-*.shs`. It is ORPHANED when a BFS from the real roots
(`.github/workflows/*`, `scripts/hooks/*`,
`scripts/check/pre-push-conflict-tree-guard.shs`) over broad textual
referrer->basename edges does not reach it. This is
`check-guard-wiring.shs`'s own model, so the number is reproducible by
running it.

| Quantity | At 66974acc | Prior sweep |
|---|---|---|
| Guards total | 422 | 413 |
| Invoked from a hook or CI | 55 | 49 |
| Orphaned | **367** | 364 |
| Listed in `guard_wiring_optout.txt` with a reason | 360 | 364 |
| **Orphaned AND unexcused** | **7** | n/a |

The "~360" figure is CONFIRMED, not refuted: 367 vs 364 is drift from nine
guards added since the earlier measurement. The number that matters for action
is not 367 but **7** — the guards that are orphaned *and* carry no written
reason. The other 360 are declared non-gates (QEMU boots, GPU/DirectX
readbacks, Electron/Bun bitmap captures, FPGA and RISC-V hardware lanes).

### Classification of the 7

| Guard | Class | Disposition |
|---|---|---|
| `check-memory-deallocation-ownership.shs` | dead, CI-capable | WIRED |
| `check-rt-free-abi.shs` | dead, CI-capable | WIRED |
| `check-module-surface-hint-scan-fast-path.shs` | dead, CI-capable | WIRED |
| `check-bootstrap-progress-watch.shs` | dead, CI-capable, **rotted** | WIRED + repaired |
| `check-gpu-runnable.shs` | needs a built `bin/simple` | open |
| `check-utf8-slice-audit-live.shs` | needs a built `bin/simple` | open |
| `stage4-diagnostic-two-phase.shs` | not a gate; a diagnostic corpus sweep | open, likely misfiled under `scripts/check/` |

Four were wired into `.github/workflows/repo-hygiene.yml` (`code-idiom-gates`).
No opt-out line was added and no baseline was touched.

### Truth reveal

`check-bootstrap-progress-watch.shs` was RED against a watcher that works
correctly. Its live-sample assertion ended in `main_log_bytes=3$`, anchoring on
that field being LAST on the line. `bootstrap-progress-watch.shs` later gained
`phase`/`unit_kind`/`done`/`total`/`tasks_*`/`failed`/`cached`/`current`/
`terminal`, moving `main_log_bytes` into the middle of the sample. Nothing ran
the guard, so the drift was never reported.

This is the decay mode of an orphaned guard: it does not merely fail to catch
things, it silently stops being runnable, so wiring it later looks like a
regression. Repaired by matching `main_log_bytes` as a whole FIELD
(`main_log_bytes=3( |$)`), which still rejects `main_log_bytes=30`. Exactness
preserved; only the coupling to field ORDER removed.

### Non-vacuity evidence

Each wired guard was proved live by sabotaging the IMPLEMENTATION it guards —
never a shim — and confirming red, then reverting and confirming green:

| Guard | Sabotage | Result |
|---|---|---|
| bootstrap-progress-watch | watcher stops parsing `milestone` from the state file | FAIL |
| bootstrap-progress-watch | watcher reports a skewed byte count | FAIL |
| bootstrap-progress-watch | stale-PID path exits 0 instead of 3 | FAIL |
| memory-deallocation-ownership | `nogc_sync_mut` arena free call renamed | FAIL |
| memory-deallocation-ownership | `rt_free` widened to two parameters | FAIL |
| rt-free-abi | Cranelift `RuntimeFuncSpec` `rt_free` given arity 2 | FAIL |
| module-surface-hint-scan-fast-path | marker widened to `# Re-exported` | FAIL |

### Refuted hypothesis

`check-workspace-root-guard.shs` (CI-wired) initially appeared FAIL-OPEN: three
undeclared-entry sabotages all returned exit 0. **That was a false positive of
my own scan.** The sabotage files were staged with `git add -N`, which makes
them tracked, and the guard deliberately grandfathers tracked entries outside
`--strict`. Re-run with genuinely untracked files, it fires correctly:

    untracked root file      -> WRG001, exit 1
    untracked src/ child     -> WRG003, exit 1
    untracked test/ child    -> WRG003, exit 1
    clean control            -> exit 0

The guard is live. Recorded because a scan's false-positive rate is a finding:
staging a fixture can silently move it into a guard's grandfathered set.

## Backlog 2 — dangling references

**Predicate.** `check-dangling-references.shs` over tracked `.spl` under `src/`
(vendored trees excluded per CLAUDE.md Owned-Code Scope): a `use` naming a
module no file provides, a `self.foo(...)` defined nowhere, or an imported name
declared by no file at all.

| Category | Count |
|---|---|
| SYMBOL — imported name declared in no src file | 112 |
| MODULE — `use` of a module no file provides | 48 |
| METHOD — `self.foo()` defined nowhere | 13 |
| **Total** | **173** |

The "~171" figure is CONFIRMED. The guard is itself opted out of wiring
(`guard_wiring_optout.txt:69`) because it is red; the backlog was 297 at
`76c3e1e080d`, so it is being driven down.

### False-positive rate: 0%

Re-derived independently by indexing every `fn|class|struct|enum|type|val|
const|me|trait|mixin` declaration across owned `src/**.spl` and intersecting:

    distinct symbols flagged                94
    actually declared somewhere in src       0
    declared nowhere                        94
    false-positive findings           0 / 112  (0.0%)

**These are all real.** PROVED.

### The important split

    imported AND used in the importing file   111 / 112
    imported but never used (safe drop)         1 / 112

This backlog is **not** stale-import cleanup. 111 of 112 are live call sites
against symbols that exist nowhere in the tree. Deleting the imports would
delete working-looking code; implementing 94 missing symbols is a program.
Neither is a silent-fix. Largest cluster: `std.async_core` (12 imports across
`src/lib/nogc_async_mut/async_host/`) — `Poll`, `CancellationToken` and
`TaskState` exist under `src/lib/nogc_async_mut/async/`, but `AsyncError` and
`Priority` exist nowhere in that tier, so the aggregator module cannot be
reconstructed by re-export alone. Target ambiguous; filed, not guessed.

## Backlog 3 — FILE.md manifests (found while checking backlog 2)

All 11 child manifests linked from the root `FILE.md` exist. PROVED. But
`--strict` (grandfathering off) reports **120** tracked entries that no
manifest declares:

| Code | Count | Meaning |
|---|---|---|
| WRG001 | 2 | root entry not allowed by `FILE.md` |
| WRG002 | 19 | immediate root child not declared |
| WRG003 | 99 | entry not declared by its parent manifest |

Concentrated in `doc/06_spec` (55), `test` (11), `scripts` (11), `bin` (9).
These are invisible in normal mode because tracked entries are grandfathered —
enforcement applies only to NEW untracked paths.

**Repaired here:** `src/hardware` and `src/i18n` are tracked directories (30
files, and `src/i18n` is named in CLAUDE.md's structure section) declared by
neither `FILE.md` nor `src/FILE.md`. Both added; WRG003 99 -> 97. Proved by
sabotage: deleting the `i18n` row re-flags it, restoring it clears.

**Also found, not repaired:**

1. Six root-manifest entries name paths that are absent and not gitignored:
   `test/06_fuzz`, `test/07_security`, `test/08_web_platform`, `tools/jupyter`,
   `tools/ref_crypto`, `bin/simple.bootstrap_seed_wrapper.c`. As allowlist
   rows they cause no failure, but they describe a tree that no longer exists.
   Not deleted unilaterally: another lane may be mid-creation, and shrinking an
   allowlist can redden someone else's CI. Needs a decision, not a guess.
2. `check-workspace-root-guard.shs` does not use `git ls-files -z`, so a path
   git must C-quote is prefix-extracted with its opening quote attached. One
   such entry shows up as the bogus root violation `"doc`. A robustness gap in
   the guard, not a tree defect.

## Not done

- The 360 excused orphans were not re-litigated one by one.
- 111 live references to undefined symbols need an owner and a plan.
- The 120-entry manifest backlog needs an owner; do not baseline it.

---

# Pass 2 — the census itself was wrong, and two clusters are repaired

- **Measured at:** `5b459977a328bb88c57d5602b9da95e26fe327d5`, tree 109,688
- **Date:** 2026-08-02
- **Binary used for every runtime claim:**
  `bin/release/x86_64-unknown-linux-gnu/simple`, which self-identifies on
  startup as the **Rust bootstrap seed** — there is no pure-Simple binary on
  this host. Every runtime result below is seed-path evidence and is labelled
  as such. No bootstrap was run.

## The headline correction: 173 was an UNDER-count, not the backlog

`check-dangling-references.shs` was **fail-open for an entire class of
missing symbol**. Its index rule for "indented bare names: struct/class
fields and enum variants"

    if (match(line, /^[ \t]+[A-Za-z_][A-Za-z0-9_]*[ \t]*[:(]/))

was applied to **every line of every file**, not only inside a type body. In
a function body that pattern matches an indented **call statement**, so the
callee was entered into the definition index. A function that exists nowhere
in the tree therefore **defined itself away** at its own call site.

PROVED, minimal reproduction:

    fn caller() -> i64:
        definitely_not_declared_xyz(1)
        return 0
    -> emit_def -> definitely_not_declared_xyz

PROVED in the real tree: `src/app/dashboard/dashboard_collectors.spl` imports
`itos` and `write_table` from `app.dashboard.main`. Neither name is declared
anywhere in the repository — `grep` for a declaration of either returns zero
files across all of `src`, including non-`.spl` sources. Both were **absent
from the 112**, because both are called as indented statements.

Fixed by tracking the enclosing type body (`in_type_block`), entered on a
`struct|class|enum|trait|mixin|union|...` declaration and left on dedent or
on a `fn`/`me` declaration. This narrows the rule to what its own comment
always said it covered. **No gate was weakened; a fail-open hole was closed.**

Non-vacuity of the fix, by before/after on a fabricated import whose callee
is called from an indented line:

| Guard version | Detected |
|---|---|
| original | **0** — missed |
| fixed    | **1** — reported |

### Honest counts

| Tree | Guard | Total |
|---|---|---|
| pristine | original (fail-open) | 173 |
| pristine | **fixed** | **225** |
| after this pass | fixed | **204** |

So the real backlog was **225**, not 173 — the census under-reported by 23%.
The 94-distinct-symbol figure is likewise a floor. **25 additional distinct
symbols** surfaced; all 25 were checked for a declaration under any
declaration form and **0 were false positives**.

## Resolution semantics — measured, not read

The prior lane's flat-global-registry hypothesis is **CONFIRMED but SCOPED**
(seed path, fixtures under `probe/`):

| Fixture | Result |
|---|---|
| call a fn declared in an imported module but NOT in the import list | **resolves**, exit 0 |
| call a fn in a module never imported | `error[E1002] ... not found`, **exit 1** |
| import a nonexistent NAME from a real module, then call it | `error[E1002]`, **exit 1** |
| import a nonexistent MODULE | `error: semantic: Cannot resolve module`, **exit 1** |

So importing *anything* from module M registers all of M's top-level
functions — but that can never rescue a symbol declared in **no** module.
**Class (d) is therefore refuted for the whole backlog**: every entry is a
real missing declaration, and every one already fails **loudly and with a
non-zero exit**. That is the bar any fix must not regress, and it is why no
stub was written for anything not implemented below.

## Cluster 1 — `std.async_core`: FIXED (12 importers, 5 symbols)

Class (b), genuine missing module. The module `std.async_core` existed
nowhere; 12 files across `src/lib/nogc_async_mut/` imported it.

Confirmed the prior lane's reading: `Poll`, `TaskState` and
`CancellationToken` live under `src/lib/nogc_async_mut/async/`, while
`AsyncError` and `Priority` exist nowhere in the tier — the only `AsyncError`
is a compiler diagnostic struct in `20.hir/hir_lowering/async_errors.spl`
and the only `Priority` is an OS scheduler struct in
`os/services/sched_service.spl`. Neither is the right type.

Added `src/lib/nogc_async_mut/async_core.spl`, which declares the two missing
types and re-exports the other three. Both new types have a contract fully
determined by existing call sites, so nothing was guessed:

- `AsyncError` — variants `CapacityExceeded`, `Timeout`, `JoinError(text)`,
  the exact set constructed across the tier.
- `Priority` — `Critical|High|Normal|Low` plus `to_i32`. The scheduler in
  `async_embedded.spl` selects with `if pri < best_priority`, so **Critical
  must be 0**; an inverted order would silently mis-schedule rather than
  fail. That ordering is pinned by a test.

`TaskState` is re-exported from `async/task.spl` (`Pending|Running|
Suspended|Completed|Cancelled`), **not** from `async/runtime.spl`, which
declares an unrelated generic `TaskState<T>`. The importers use exactly the
first enum's variants.

Spec: `test/01_unit/lib/async_core_spec.spl` — 7 examples, 0 failures.
Sabotage (implementation, not spec): inverting the `Priority` keys reddens 2
examples; repointing `TaskState` at the generic enum reddens 1; both restore
green.

## Cluster 2 — `std.common.unicode.codepoint`: FIXED (8 symbols, 14 call sites)

Class (b). `src/lib/common/encoding/unicode_text.spl` imported eight
codepoint predicates from a module that did not exist and called them from 14
sites, so `utext_to_upper`, `utext_is_alpha`, `utext_trim` and friends were
all dead on first call.

Added `src/lib/common/unicode/codepoint.spl` as an explicit range table —
the same approach `encoding/text_ops.spl:codepoint_script` already uses in
this tier — with the covered blocks documented in the module header rather
than implied. Case mapping is simple (1:1); characters with no simple
uppercase (U+00DF, U+0138, U+0149) are returned **unchanged**, which is what
simple case mapping specifies, instead of being mangled.

The Latin Extended-A block is the trap: its upper/lower parity **flips twice**
(even-upper to U+0137, odd-upper to U+0148, even-upper to U+0177, odd-upper
to U+017E). A single even/odd test is wrong for a third of the block; the
segmentation and the U+0130/U+0131/U+017F/U+0178 specials are handled and
pinned.

Spec: `test/01_unit/lib/unicode_codepoint_spec.spl` — 12 examples, 0
failures, all expectations hand-computed from the Unicode simple case
mappings. Sabotage: collapsing the parity flips to a naive even/odd test
reddens the Latin Extended-A example; folding U+00DF into the Latin-1
subtract-0x20 range reddens the no-simple-uppercase example; both restore
green.

End-to-end through the real consumer (seed path), which previously failed:

    utext_to_upper("αβγ")   -> ΑΒΓ
    utext_to_lower("АБВ")   -> абв
    utext_is_alpha("日本語") -> true
    utext_trim(NBSP hi NBSP) -> "hi"
    utext_is_upper("ÄÖÜ")   -> true

## Refuted hypotheses

1. **`app.dashboard.main` was gutted by one of the tree-wipe commits.**
   REFUTED. `main.spl` is 14 lines at every commit where it is non-empty
   across its whole history; it was never larger. The 18 names imported from
   it were never declared there.
2. **The `std.async_core` cluster is unfixable by re-export.** Half right,
   and worth restating precisely: re-export alone is insufficient because two
   of the five types exist nowhere, but a module that *declares those two and
   re-exports the other three* is exactly the right shape. Filing rather than
   guessing was correct; the contract was recoverable from call sites.
3. **The census over-reports.** REFUTED in both directions — 0 false
   positives confirmed again, and it additionally **under-reports** by 23%.

## Remaining backlog — 204, classified by cluster

Largest SYMBOL clusters still open (module -> count):

| Import target | Count | Notes |
|---|---|---|
| `app.dashboard.main` | 18 | Class (b). SDN table load/write + date helpers. `main.spl` is a 14-line CLI entry that never declared them. Needs a real `dashboard/tables.spl`; the contract is recoverable from call sites but it is a day of work, not a repoint. |
| ~~`std.error`~~ | ~~16~~ | **Withdrawn in pass 3 — all 16 were false positives.** `SimpleError` is declared as `extern class`, which the guard could not see. The real defect is a constructor link failure, filed separately. |
| `std.math.bignum.bignat` | 8 | `bn_zero`, `mod_exp`, `to_bytes_be`, `modulo`. Crypto-adjacent — **must not be stubbed**; a wrong bignum is a silent security defect. |
| `compiler.core` | 7 | Newly surfaced. |
| `common.window_protocol.window_protocol` | 7 | `WM_*` constants + `wm_input_event`. |
| `std.{nogc,gc}_async_mut.js.engine.interpreter` | 4 + 4 | Same symbol set imported from two tiers. |
| `common.display_protocol.display_protocol` | 4 | |
| `std.report.emitter.lsp` | 3 | `LspEmitter`, imported by two CLI files. |
| `std.random_utils` | 3 | `rng_next_range`, `variance_sample`. |
| `host.common.io.types` | 3 | |
| `compiler.tools.leak_check.types` | 3 | |
| `app.build.quality` | 3 | Also a MODULE finding (3 importers). |
| `app.build.baremetal` | 3 | `baremetal_config_riscv`, `baremetal_config_riscv32`. |

MODULE findings still open (35), largest: `host.common.io.fs_ffi` (4),
`ui.element` (3), `app.build.quality` (3), `ui.tui.renderer_async` (2),
`ui.patchset` (2), `ui.attrs` (2), `std.common.math.field.fe_p256` (2),
`simple_sdn` (2). METHOD findings: 17.

## Not done — stated plainly

- **11 of 13 symbol clusters are untouched.** Only `std.async_core` and
  `std.common.unicode.codepoint` are repaired. 204 of 225 remain.
- The `std.error` and `compiler.core` clusters (23 findings) surfaced only
  after the guard fix and have had **no** triage beyond being counted.
- No cluster was found to be class (a) (wrong import, symbol exists
  elsewhere) or class (c) (dead caller). Both were looked for and neither
  appeared in the two clusters examined; the remaining clusters were not
  checked for them.
- `check-dangling-references.shs` stays opted out of CI. It is now red at a
  larger and more honest number; **do not baseline it**, and do not re-close
  the fail-open hole to make the number smaller.
- All runtime evidence is **seed-path only**. Re-verification on a
  pure-Simple binary is owed once one exists.

## Side finding — the linter's own auto-fix introduces a dangling reference

`bin/simple lint` emits SPIPE007 on `expect(bool).to_equal(false)` and offers
a **safe auto-fix** to `expect_not(condition)`. Applying it reddened five
examples with:

    semantic: function `expect_not` not found

`expect_not` *is* declared -- `src/lib/nogc_sync_mut/spec.spl:533` and
`src/compiler_rust/lib/std/src/spec/expect.spl:73` -- but it is not reachable
from a spec on the run path used here, where the assertion vocabulary comes
from intrinsics rather than the `.spl` spec libs. `assert_true` and
`assert_false` are reachable; both were confirmed non-inert by a probe spec
that asserts a true condition with `assert_false` and observes it FAIL.

So SPIPE007's suggested fix is, on this path, a recipe for exactly the defect
this bug is about. Filed, not worked around: the specs here use
`assert_false`, and SPIPE007 needs either a reachable `expect_not` or a
changed suggestion. 282 existing `expect_not(` call sites in `test/` are
presumably affected the same way and were NOT audited.

---

# Pass 3 — the census ALSO over-reports: `extern class` is invisible to it

The pass-1 claim **"false-positive rate 0%, these are all real"** is
**REFUTED**. The guard's type-declaration rule was

    /^[ \t]*(pub[ \t]+)?(export[ \t]+)?(struct|enum|class|...)[ \t]+NAME/

which permits only `pub` and `export` as prefixes. It therefore does not match

    extern class SimpleError:

PROVED by running the guard's own regex against that exact line: **NO MATCH**.
There are **20** `extern`-prefixed and **2** `abstract`-prefixed type
declarations in `src`, all invisible to the index. (The other leading words a
naive `[a-z]+` prefix would pick up — `this`, `the`, `where`, `widget` — are
prose inside comments and docstrings, so the fix names `extern` and `abstract`
explicitly rather than generalising.)

Effect: **16 of the reported findings were false positives**, every one of
them `SimpleError`, imported across `src/lib/gc_async_mut/net/`. After the fix
the count drops 204 -> 188 and the diff of findings is exactly those 16
removed, **0 added**.

Both guard fixes were then verified together on one run, since the second
could have re-opened the first:

| Probe | Want | Got |
|---|---|---|
| absent symbol called from an indented line | reported | **1** |
| `extern class` type consumed by another file | not reported | **0** |

## The real defect behind those 16

`SimpleError` is declared twice and its constructor **does not link**:

    error[E1002]: function `SimpleError` not found
    HIR lowering: cannot infer field type ... struct 'SimpleError' field 'message'

**Refuted: the import path is wrong.** `use std.error` and
`use std.common.error` fail **identically** — the module and the `error`
function both resolve; the `SimpleError(...)` construction inside `error()` is
what fails. Repointing fixes nothing, so this is **not** class (a).

Filed as `doc/08_tracking/bug/extern_class_constructor_not_found_simpleerror_2026-08-02.md`.
Not stubbed: a shadowing plain `class SimpleError` would compile and return an
object that is not what the SFFI boundary hands back — a silent wrong answer
traded for a loud failure.

## Corrected running totals

| Tree | Guard | Total |
|---|---|---|
| pristine | pass-1 guard (fail-open, extern-blind) | 173 |
| pristine | both fixes | **209** |
| after passes 2-3 | both fixes | **188** |

So the pass-1 figure of 173 was wrong in **both** directions at once: it
missed 52 real findings and invented 16 that were not real. The corrected
pristine backlog is 209. Two clusters were then genuinely fixed (`async_core`
12, `unicode.codepoint` 8) and one cluster of 16 dissolved as measurement
error, leaving 188.

**Lesson worth keeping:** a census whose declaration index is a regex will be
wrong in both directions, and a "0% false positives" claim derived by
re-running a *similar* regex is not independent — pass 1's re-index used the
same prefix assumption and so inherited the same blind spot. Confirming a
census against a second copy of its own model confirms nothing.

## Re-verification 2026-08-17

```
$ ls -la scripts/check/check-extern-registration.shs
```

## Re-verification 2026-08-17 — `check-extern-registration.shs` narrow check

This session's assignment cites `scripts/check/check-extern-registration.shs`
specifically. That file exists (`ls -la` confirms, 9782 bytes, executable,
mtime Aug 11), and is **no longer orphaned**: it is now invoked directly from
CI —

```
$ grep -n "check-extern-registration" .github/workflows/repo-hygiene.yml
203:          sh scripts/check/check-extern-registration.shs
```

— which is one of this doc's own declared "real roots"
(`.github/workflows/*`). So for this one guard specifically, Backlog 1
("orphaned guard") is **resolved** as of the current tree; it would no longer
appear in a fresh `check-guard-wiring.shs` orphan count reachable-from-root
BFS. Per `check_script_wiring_orphans_2026-08-01.md:179`, it remains wired
**report-only** (no `--strict`, so it cannot fail the workflow) — that
report-only gap is a separate, still-open concern the doc's Backlog 2
discussion already covers, not a dangling reference.

No source changes made (guard-wiring status is a workflow-file fact, not an
`src/app/**`/`scripts/check/**` code defect to fix). This narrow finding does
not resolve the doc's two backlogs in general (367/7 orphaned-and-unexcused,
per the table above) — only the one guard named in this session's row is
confirmed no longer orphaned.

# Architecture / style rule audit of the 2026-08-09→10 landing window

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Audit surface:** 910 files changed across 388 commits in the trailing 20h on
`origin/main` (tip `45e486f0be6`), of which 330 were newly added. 586 `.spl`,
158 `.md`, 56 `.rs`, 51 `.shs`, 13 `.c`.
**Method:** all checks run against the fetched origin tip via `git cat-file`,
not the shared working copy.

## Clean (verified, non-vacuous)

| Rule | Result | Evidence |
|------|--------|----------|
| NO inheritance | CONFORM | 249 changed `src/**.spl` scanned for `extends` / `superclass` / `super.`; 8 hits, **all prose comments** (e.g. `50.mir/_MirLoweringExpr/method_calls_literals.spl:2816` "zero-extends"). Zero declarations. |
| Generics `<>` not `[]` | CONFORM | 0 hits for `(List\|Dict\|Map\|Set\|Option\|Result\|Array\|Vec)\[[A-Z]` across the same 249 files. `[HtmlToken]` etc. are array-type syntax, not generic instantiation. |
| No new Python | CONFORM | 0 `.py` added. |
| TODO/FIXME → NOTE | CONFORM | 1 removed TODO line in tonight's `src/**.spl` diffs; it is a *completed* item (`TODO #87 ✅`), not a downgrade. |
| workspace-root-guard | PASS | `sh scripts/check-workspace-root-guard.shs` → `workspace-root-guard: OK`, exit 0. No new directory required a `FILE.md` it lacks. |
| `__init__.spl` integrity | CONFORM | 9 `__init__.spl` changed tonight; 47 `export <module>.*` re-export targets resolved against the tip — **0 dangling**. |
| Revert-recovery completeness | CONFORM | 143 `use std.*` imports from the 330 newly-added spec files resolved — 0 orphans. The only files *deleted* tonight are the 4-tier `service/request_queue.spl` set plus its 2 specs, and `git grep request_queue` over `src/**`/`test/**` at the tip returns only unrelated hits (`transport_request_queued`) and vendored Rust. Clean dedupe, nothing half-restored. |

## Finding 1 — two new Perl scripts violate "ALL code in `.spl`/`.shs`"

`9a0cfd1e5d6` ("fix(bootstrap): harden staged native compilation") added:

- `scripts/check/lib/portable-hardlink-lock.pl`
- `scripts/check/lib/portable-session-exec.pl`

Perl is not one of the three grandfathered bootstrap scripts and is not `.shs`.
This is a genuine new-tonight violation of the root `CLAUDE.md` rule. Not fixed
here: both implement process/hardlink locking primitives, and a blind
transliteration to `.shs` risks breaking the bootstrap lock semantics they were
added to harden. Needs the original author or a scoped port with a lock-race
test.

## Finding 2 — `≤10 files per directory` exceeded

- **New tonight, marginal:** `test/03_system/language/value_semantics/probe` —
  11 files. One over; a single split fixes it.
- **Pre-existing, gross:** `scripts/check` holds **585** files (30 added
  tonight), `src/app/io` 73, `src/compiler/35.semantics/lint` 53, `src/os/port`
  35. Tonight's commits did not create these but did enlarge them. The
  `≤10-files-per-directory` rule is currently unenforced by any guard —
  `check-workspace-root-guard.shs` checks `FILE.md` manifests, not fan-out. That
  gap is why this drifted this far unnoticed and is the more valuable fix.

## Finding 3 — `src/lib/blink/**` does not use the ECS layer (PRE-EXISTING, not a regression)

MDSOC+ (`doc/04_architecture/compiler/mdsoc/mdsoc_architecture_tobe.md:370-393`)
requires userland libs to be an MDSOC capsule outside with an ECS business layer
inside: a `World`, POD components in `ComponentStore<T>`, systems as free
`(world, dt)` functions, `use std.ecs`.

`grep -rE "World|Entity|ComponentStore|use std.ecs" src/lib/blink/` returns
**zero hits across the entire blink tree** — old and new alike. There is also no
`src/lib/blink/__init__.spl` and no capsule manifest. Tonight's additions
(`blink/paint/`, `blink/html_parser/`, `blink/style/`) follow the established
blink convention of plain modules + free functions over parallel arrays.

**This is explicitly not a tonight regression.** The new code is in fact *closer*
to ECS shape than its predecessors: `layout/style_bridge.spl:101-105`
(`StyledLayout` = `node_ids: [i64]` + `styles: [ComputedStyle]`) is genuine SoA
columns keyed by node id, and `paint/style_paint.spl:25-44`
(`paint_chunks_from_styled_layout`) is exactly a system-shaped free function over
them. Filed against `src/lib/blink/**` as a whole, not against tonight's commits;
adopting `std.ecs` here is a directory-wide migration and must not be done
unilaterally.

Sub-items observed while checking:
- Over-engineering: **none**. Zero traits in all of `src/lib/blink/**`, so no
  one-implementor trait; no factories; no config structs. `style_paint.spl` is 46
  lines; `cascade.spl:24-40` documents its non-goals rather than speculatively
  building them.
- Minor inconsistency: new `paint/` and `style/` ship no `__init__.spl` while
  `html_parser/` and `css_parser/` do — though `dom/`, `entity/`, `layout/`,
  `url/` also lack one, so it matches the majority pre-existing state.
- Perf note (not a rule violation): `style_bridge.spl:107-115` `style_for` does a
  linear scan over `node_ids` per lookup — O(n²) in document size. An ECS
  `ComponentStore` would make this O(1), which is the strongest concrete
  argument for the migration above.

## Overall verdict

The night's work is **architecturally sound**. Across 910 changed files the two
hard language rules (no inheritance, `<>` generics) hold with zero violations,
the revert-recovery left nothing structurally half-restored, and the enforced
workspace guard passes. One real new violation (Perl scripts) and two
pre-existing structural gaps (directory fan-out, blink/ECS) are filed above.

## Addendum: Perl-scripts finding re-examined — the split was deliberate

A follow-up pass investigated porting the two `.pl` files and found the original
framing was incomplete. Commit `9a0cfd1e5d6` did **not** add two orphan Perl
scripts. It added them together with `scripts/check/lib/portable-process-lock.shs`
— an already-`.shs` orchestration layer doing claim files, manifest parsing,
the deadline loop, stale-recovery protocol, and release-all bookkeeping — which
calls the Perl helpers via `PORTABLE_LOCK_ATOMIC_HELPER_PATH`. **The prior
author already performed the natural split and left only the two genuinely
delicate atomic primitives in Perl.**

What those primitives actually do, and why they are delicate:

- `portable-hardlink-lock.pl` — atomic `link(2)` create-or-fail; dev:ino
  identity via `lstat` (rejecting symlinks); and PID-liveness via a **double
  `ps -o lstart=` snapshot bracketing a `pgid` read**, so a snapshot is trusted
  only if `lstart` is unchanged before and after. That construction exists
  specifically to defeat PID-reuse TOCTOU — it is not incidental.
- `portable-session-exec.pl` — `setsid()` a new session leader and `exec` into
  it, with a fork-fallback for the legitimate `EPERM` case where the caller is
  already a process-group leader, so lock ownership binds to an independently
  recoverable session rather than the parent's process group.

**Portability determination: technically possible, not free.** `ln` provides the
same atomic `link(2)` create-or-fail; the double-snapshot liveness pattern is
expressible via command substitution; the `unlink-if-match` manifest check is
already duplicated in `.shs`. The one real gap is `stat`'s dev/inode flags
differing GNU (`-c`) vs BSD/macOS (`-f`), needing a platform-detect shim — a
portability chore, not an unavailable primitive.

**Recommendation (needs a human decision, not an agent's):** grant a scoped,
documented exception to the `.spl`/`.shs`-only rule for exactly these two files,
on the grounds that they are an intentionally-minimized atomic-primitive layer
beneath an already-conforming orchestration layer. Reserve an actual port for a
session with budget to run the full differential suite — N-simultaneous-acquire
(exactly one winner per round), kill-and-reclaim (stale lock recoverable), and
clean-exit-release — side by side against the Perl original **before** any `.pl`
is deleted.

**Explicitly not done:** no port was attempted. This is live bootstrap-lock
infrastructure that concurrent sessions are exercising right now; a blind swap
of atomic primitives under live locks, unproven by concurrency testing, would
risk corrupting other sessions' builds. A correct Perl script beats a subtly
racy `.shs` one.

## Lane J re-verification 2026-08-17 (classified by CONTENT, not SHA ancestry)

**Verdict: STILL-OPEN (reproduced by content).** Both Perl files are still on disk:
`scripts/check/lib/portable-hardlink-lock.pl` (3729 bytes) and
`scripts/check/lib/portable-session-exec.pl` (2209 bytes), violating the
`.claude/rules` 'ALL code in .spl/.shs' rule. They are live dependencies, not dead
files — referenced by `scripts/check/lib/portable-process-lock.shs`,
`scripts/check/check-bootstrap-portability.shs` and
`scripts/bootstrap/bootstrap-from-scratch.sh`, so deleting them is not the fix;
a POSIX-sh reimplementation of hardlink locking / session exec is required.
Not attempted this session (out of the silent-wrong-result scope of this lane).

# Architecture / style rule audit of the 2026-08-09→10 landing window

**Status:** OPEN (3 findings, all filed — none fixed unilaterally)
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

# Plan — reject Option patterns on non-Option scrutinees (staged migration)

- **Date:** 2026-09-27
- **Owner ruling (2026-09-27):** staged migration. New code gets the error first;
  existing sites are converted in batches; the check then becomes a hard error
  everywhere.
- **Bug:** `doc/08_tracking/bug/option_pattern_accepted_on_non_option_scrutinee_2026-07-27.md`
- **Todo:** 339, `doc/08_tracking/todo/option_pattern_non_option_scrutinee_migration_2026-09-27.md`
- **Acceptance spec:** `test/01_unit/compiler/interpreter/option_on_non_option_scrutinee_class_spec.spl`
  (tagged `@tag:in-development` until stage 3 lands; the tag comes off when it passes).

## Why staged

`Some(_)` / `if val Some(..)` / `.unwrap_or` on a value whose static type can
never be an Option (a bare `i64`, `f64`, `bool`, `char`, `text`) compiles today
and yields engine-specific wrong values. The seed has a correct but warn-only
shape check, off by default: `src/compiler_rust/compiler/src/hir/lower/option_pattern_shape_diag.rs`,
enabled with `SIMPLE_DIAG_OPTION_PATTERN_SHAPE=1` (it also turns on the
interpreter's runtime twin in `interpreter_patterns.rs`). Making it a hard error
in one step would stop the bootstrap, because the tree compiles through these
paths.

Census of Option-shaped pattern sites on `origin/main` (2026-09-27, `git grep -F`,
`src/**/*.spl`): `case Some(` 2,395 in 557 files, `if val Some(` 1,081 in 248
files, `Some(_)` 102 in 71 files, `case None` 940 in 229 files. The diag
module's own figure is ~2,746 Option-shaped (plus ~4,211 Result-shaped) sites
across 620 files. Almost all of these are legitimate `T?` scrutinees. The
subset that actually trips the check (a bare scalar or text subject) is
**unmeasured**; stage 0 measures it.

## Stages

### Stage 0 — measure the real fallout
- Build every compiler, lib and app module with `SIMPLE_DIAG_OPTION_PATTERN_SHAPE=1`
  (seed native-build of the full CLI, plus `simple test` over `test/`) and collect
  the warning lines into `doc/08_tracking/todo/option_pattern_shape_sites_<date>.txt`:
  one line per site (`path:line:subject-type`).
- Output: the true offender count. Plan the batches from that count, not from the
  2,746 census.

### Stage 1 — error for NEW code (ratchet)
- Freeze the stage-0 list as a baseline (`scripts/check/option_pattern_shape_baseline.txt`).
- Add a ratchet gate in the style of `check-no-direct-rt.shs`: rerun the diag and
  FAIL when a site is not in the baseline (new debt), and also FAIL on a stale
  baseline entry (a converted site that is still listed). Register it in
  `config/check/must_check_gates.sdn` (local + extended CI tier) with its dispatch
  arm.
- In the seed, make the diag an error for any site not on the baseline when
  `SIMPLE_OPTION_PATTERN_SHAPE_STRICT=1`, and turn that on for the ratchet gate.
- Mirror the check in the pure-Simple type checker. Otherwise the self-hosted
  compiler keeps accepting what the seed rejects.

### Stage 2 — convert existing sites in batches
- Batch by owning layer and directory (≤ ~150 sites or ≤ 20 files per PR), in
  this order: `src/lib/common`, `src/lib/nogc_*`, `src/compiler/<layer>` (low to
  high), `src/app`, then `test/`.
- Each site gets one of two fixes: (a) the value really is optional, so the
  producer's return type becomes `T?`; or (b) the value is never optional, so
  the pattern is replaced with a plain comparison or binding (for example
  `index_of` returns a plain `i64` with a `-1` sentinel).
- Every batch shrinks the baseline in the same PR; the ratchet's stale-entry rule
  enforces this.
- Every batch keeps the bootstrap green (`compiler_bootstrap_tests`, interpreter
  suite) and reports the before/after site count.

### Stage 3 — hard error everywhere
- With an empty baseline, remove the gate and make the check unconditional in the
  seed and in pure-Simple. Keep the wildcard-arm fix: an interpreter `_` arm must
  always match.
- Remove `@tag:in-development` from the acceptance spec. It must pass on both
  engines, with every bad probe rejected at compile time.

## Risks
- The check only fires on bare scalar/text subjects. Unknown, `Any`, aggregate or
  pointer subjects are deliberately silent, so stage 3 does not cover them. A
  follow-up widening needs its own census.
- Stage 2 changes producer signatures (`T` -> `T?`), which can ripple across
  modules. Keep each batch's blast radius visible in the PR.

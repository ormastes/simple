# The TODO scanner accepts only `.spl` and `.md`, so `todo_db.sdn` structurally under-reports

**Date:** 2026-09-06 · **Status:** RECORDED (needs a scoping decision, not a reflex fix) ·
**Measured at:** `a12a19eb775` (worktree checkout of `origin/main`). No build was run.

## The filter

`src/app/todo_scan/main.spl`, `fn should_scan(path: text) -> bool` at **line 266**, ending
at **line 284**:

```
fn should_scan(path: text) -> bool:
    # Skip build artifacts, hidden dirs, etc.
    if path.contains("/target/"):
        return false
    if path.contains("/build/"):
        return false
    if path.contains("/.git/"):
        return false
    if path.contains("/node_modules/"):
        return false
    if path.contains("/archive/"):
        return false

    # Only scan known source file types
    if path.ends_with(".spl"):
        return true
    if path.ends_with(".md"):
        return true
    false
```

Two accepted extensions. A `TODO` or `FIXME` in a `.rs` file or a `.shs`/`.sh` script is
not merely deprioritised — it is never read, so it can never appear in
`doc/08_tracking/todo/todo_db.sdn` or `doc/TODO.md`. The database is not incomplete by
accident; it is complete with respect to a filter that excludes two of the repository's
languages.

That matters in this repo specifically. `.claude/rules/commands.md` establishes that
`bin/simple todo-scan` is the tool that maintains both artifacts, and CLAUDE.md's
"NEVER convert TODO to NOTE — implement or delete" rule is enforced against a tracker that
cannot see the Rust seed (`src/compiler_rust/**`, the bootstrap-critical lane) or any of
`scripts/**`, where the entire check/gate suite lives.

## The `.rs` arm exists, in the wrong binary

```
src/compiler_rust/driver/src/todo_db.rs:480:                if ext == "rs" || ext == "spl" || ext == "md" {
```

So a three-extension filter was written and is sitting in the Rust driver. It is not the
code that runs: `src/app/cli/dispatch/table.spl:378-379` routes the `todo-scan` command to
`app_path: "src/app/todo_scan/main.spl"`, the two-extension implementation above.

**Hedge, stated rather than glossed:** "dead path" is a claim about which binary services
the command on a given host, and the dispatch table is the evidence for the pure-Simple
route. On *this* host `bin/simple` resolves to a 2026-09-05 bootstrap artifact (see
`deployed_seed_predates_tip_verification_cap_2026-09-06.md`), which is a seed build, so
whether an invocation here reaches the Rust arm or the Simple arm was **not** determined
empirically — `todo-scan` was not run. What is established is that the sanctioned route per
the dispatch table is the two-extension one, and that the two implementations disagree.
That disagreement is itself worth recording regardless of which one executes.

## Why this is filed rather than fixed

Widening `should_scan` is textually a one-liner. It should not be done as a reflex, for a
concrete reason: `should_scan` has **no `/vendor/` exclusion**. Its five skip rules are
`/target/`, `/build/`, `/.git/`, `/node_modules/` and `/archive/`. CLAUDE.md's Owned-Code
Scope explicitly excludes `src/compiler_rust/vendor/**` and `src/runtime/vendor/**` from
counts, reviews and scans. Adding `.rs` without adding a vendor exclusion would pull every
TODO in the vendored Rust crates into `todo_db.sdn` in one pass — a large, unowned import
that would swamp the real signal and violate the owned-code rule the moment it landed.
(`/target/` catches build output, not checked-in vendor source.)

So the change is at least two coupled edits, and the scope of the second is a decision:

1. Which extensions to admit — `.rs` alone, or `.shs`/`.sh` too, given that
   `.claude/rules/*` mandates all shell be `.shs`.
2. What to exclude — `/vendor/` at minimum; possibly also `src/compiler_rust/**` wholesale
   if the seed is considered out of the tracker's remit, which would be a narrower and
   safer first step than admitting the whole Rust tree.
3. Whether to reconcile or delete `todo_db.rs`'s divergent filter, so the two
   implementations stop disagreeing.

## What was NOT established

- **No size estimate.** How many TODO/FIXME comments would be admitted by each candidate
  scoping was not counted, in owned code or in vendor. Without that number the "would swamp
  the signal" concern above is a reasoned expectation, not a measurement, and the decision
  in the previous section should be made against real counts.
- **`todo-scan` was not executed**, so the current `todo_db.sdn` was not regenerated and no
  before/after comparison exists.
- **No survey of what would be found.** Whether the Rust seed and `scripts/**` actually
  carry meaningful TODOs — as opposed to few or none — is unknown. It is possible the
  under-reporting is structural but empirically small. That would change the priority, not
  the correctness of the finding.

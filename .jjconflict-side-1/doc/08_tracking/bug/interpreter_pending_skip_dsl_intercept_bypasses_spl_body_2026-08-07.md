# Rust seed interpreter intercepts `pending`/`skip_it`/`skip` calls before `.spl` body runs

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- Found: 2026-08-07, while landing WP-9 (skip governance,
  `doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`)
- Files:
  - `src/compiler_rust/compiler/src/interpreter_call/bdd.rs:782` — `"pending" | "pending_it" =>` match arm
  - `src/compiler_rust/parser/src/test_analyzer.rs:58` — `SKIP_TEST_FUNCTIONS = ["skip_it", "skip", "skip_test", "pending"]`
  - `src/lib/nogc_sync_mut/spec.spl` — `pending()`, `skip_it()`, `skip()`

## Symptom

Under `bin/simple test` (the Rust seed's BDD interpreter dispatch), a call
literally named `pending(...)` inside an `it` block is intercepted by
`bdd.rs:782` BEFORE dispatch ever reaches `std.spec.pending()` in
`spec.spl`. The intercept prints `○ <name> (skipped)` and calls
`record_test_result(desc_path, name_str, true, true)` — unconditionally
**PASSED** — with no path to the `.spl` function body at all.

Separately (pre-existing, unrelated mechanism): `spec.spl`'s `skip_it(name,
block)` and `skip(name, reason)` both start with
`if not _run_test("skipped"): return`, and `_run_test("skipped")` is only
`true` when `SIMPLE_TEST_FILTER=="skipped"`. Under any normal test run
(`SIMPLE_TEST_FILTER` unset), that guard returns immediately — the bodies of
`skip_it`/`skip` never execute either, for a different reason (test-filter
gating rather than a hardcoded name intercept).

## Consequence for WP-9 skip governance

`skip_ref(id)`/`validate_skip_it`/`validate_bare_pending`/
`validate_free_text_skip`/`validate_skip_ref_record` in
`src/lib/nogc_sync_mut/spec/skip_governance.spl` are correct and reachable —
verified directly (`bin/simple run`) and through the newly-authored
`skip_via_ref(name, id, block)` in `spec.spl`, which is NOT one of the
intercepted/gated names and DOES reach the governance path end-to-end
(reproduced below). But **`pending()`, `skip_it()`, and `skip()` themselves
cannot enforce governance under the Rust seed's `bin/simple test`** —
`pending()`'s body is bypassed entirely by the hardcoded dispatch intercept,
and `skip_it()`/`skip()`'s bodies are bypassed by the pre-existing test-filter
gate. Their `.spl`-level governance wiring is correct and will apply once
either (a) the self-hosted pure-Simple binary runs these specs without the
Rust seed's BDD intercept, or (b) a caller invokes them directly outside the
seed's dispatch table (e.g. `bin/simple run`, as reproduced below).

Per repo convention ("Default tooling = pure-Simple self-hosted binary, not
the Rust seed" — `.claude/rules/bootstrap.md`), fixing `bdd.rs` is explicitly
out of scope for this WP (`.spl`-only, no Rust changes) and would fix the
seed rather than the tool this project is migrating away from.

## Reproduction

Direct evidence, `bin/simple run` (bypasses both intercepts because `main()`
calls `skip_via_ref` directly, and `skip_via_ref` is not in
`SKIP_TEST_FUNCTIONS`/`bdd.rs`'s match arms):

```
$ SIMPLE_TEST_FILTER=skipped SIMPLE_SAFETY_PROFILE=critical bin/simple run <script calling skip_via_ref("x", "unregistered-id", fn(): ())>
    it unregistered skip ... FAILED (skip rejected under critical: skip id "nonexistent-wiring-proof-id" has no registered SDN record (category/reason/owner/expiry/issue all empty) — add doc/08_tracking/skip/nonexistent-wiring-proof-id.sdn)
wrote evidence: true
simple-bdd-v1
0
1
```

Same call under `SIMPLE_SAFETY_PROFILE=moderate`:

```
    it unregistered skip under moderate ... skipped ()
```

`pending()` under `bin/simple test` (interpreter intercept fires, ignores the
`.spl` body's rejection entirely):

```
$ SIMPLE_SAFETY_PROFILE=critical bin/simple test <spec with `it "x": pending("...")`>
  ○ bare pending, no SDN-tracked metadata (skipped)
  ✓ inner: bare pending with no SDN-tracked metadata
```

(printed "(skipped)" and counted as passed — never reached `.spl`'s
`pending()`, whose body under critical would have pushed a rejection into
`current_test_errors`.)

## Suggested owner

Compiler/interpreter team (Rust seed only; do not backport into the
self-hosted pure-Simple compiler, which has no such name-based intercept to
begin with). Options: (a) accept as a known seed-only gap now that
`skip_via_ref` gives governance a reachable path independent of the
intercepted names, or (b) have `bdd.rs`'s `pending`/`skip_it`/`skip` arms call
into the compiled `.spl` implementation instead of reimplementing BDD
bookkeeping in Rust, closing the divergence class entirely.

## 2026-08-17 re-verification (lane m1_rust_interp) — STILL LIVE, but semantically benign

Classified by CONTENT (per session CORRECTIONS #1).

The intercept is still there and is unconditional:
`src/compiler_rust/compiler/src/interpreter_call/bdd.rs:902` handles
`"pending" | "pending_it"` entirely in Rust — it prints the `○ <name> (skipped)`
line itself, pushes the name into `BDD_IGNORED_TESTS`, calls
`record_test_result(desc_path, name, true, true)`, bumps `BDD_COUNTS`, and
returns `Value::Nil`. Control never reaches the `.spl` definition in
`src/lib/nogc_sync_mut/spec.spl`.

**Assessment:** the intercept produces the SAME observable outcome the `.spl`
body is meant to produce (skipped, counted, passed=true/skipped=true), so this is
not a silent-wrong-result. The real cost is divergence risk: any future change to
the `.spl` `pending` implementation will be silently ignored under the seed. That
is a maintainability defect, not a correctness one.

**Status: OPEN, correctly P2-or-lower.** Recommended resolution is to delete the
Rust arm once the self-hosted binary is the default tool (the intercept exists
only because the seed cannot rely on the stdlib spec DSL loading), not to patch
it now.

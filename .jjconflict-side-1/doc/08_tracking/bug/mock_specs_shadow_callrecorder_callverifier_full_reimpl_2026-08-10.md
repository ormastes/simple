# mock_spec twins shadow CallRecorder/CallVerifier with a full alternate mock framework

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

- **Files**:
  - `test/unit/lib/common/mock_spec.spl:123,155` (625 lines)
  - `test/unit/std/mock_spec.spl:123,155` (593 lines, near-duplicate of the above)
- **Real product code**: `src/compiler_rust/lib/std/src/spec/mock.spl:308,347` —
  `class CallRecorder` (`static fn new()`, `me record(...)`) and
  `class CallVerifier` (`recorder: CallRecorder`, `method_name`, `VerifyCount`-based
  `times()`/`once()`/`never()`/`at_least()`/`at_most()`).
- **Found during**: continuation of the SHADOW-family spec vacuity sweep
  (worklist rows 87, 149, 150).

## What's wrong

Both specs declare their own `CallInfo`/`CallRecorder`/`CallVerifier`/
`StubEntry`/`Mock`/`Spy` mini-framework from scratch (`CallRecorder.create()`
not `.new()`, `calls: [CallInfo]` with `args: [i64]` only, `CallVerifier`
driven by a `count_type: text` string tag ("once"/"never"/"exactly"/
"at_least"/"at_most") instead of the real `VerifyCount` enum). This is not a
thin field-rename shadow — it is a complete second implementation of the
mock/spy/stub framework (500+ lines each) that happens to reuse two of the
real module's class names. Neither spec can ever catch a defect in the real
`src/compiler_rust/lib/std/src/spec/mock.spl`, since none of its real code
path executes.

## Why not fixed in this pass

Same class of finding as `narrowing_spec`/`riscv_dual_arch_spec`: importing
the real `CallRecorder`/`CallVerifier` would require deleting and rewriting
essentially the entire file (`Mock`, `Spy`, `StubEntry`, `ArgMatcher`
matching helpers all reference the local classes and would need to be
re-derived from the real `mock.spl` API, which also supports `ArgMatcher`,
`arg_any`/`arg_exact`/`arg_gt`/etc. matching that the local reimplementation
duplicates independently). This is a full-file rewrite, not a bounded
import-swap.

## Unblock condition

Rewrite both specs to import `CallRecorder`/`CallVerifier` (and `Mock`/`Spy`/
`ArgMatcher` if those exist in the real module) from
`src/compiler_rust/lib/std/src/spec/mock.spl`, dropping the local
reimplementation entirely, and confirm the existing assertions still hold
against the real `VerifyCount`-based verification semantics. Consider
deduplicating the two near-identical twin files at the same time.

## Status: FIXED 2026-08-10

Both specs now import the real classes via `use std.spec.mock.{...}`
(confirmed working import path; `use spec.mock.{...}` fails with `Module
"spec" does not export 'mock'`, and `use spec.{Mock}` — the shape used by the
pre-existing `test/unit/std/mock_simple_spec.spl` — fails at runtime with
`variable Mock not found`, both pre-existing/unrelated to this fix).

- **`test/unit/lib/common/mock_spec.spl`** (canonical): fully rewritten,
  local `CallInfo`/`CallRecorder`/`CallVerifier`/`StubEntry`/`Mock`/`Spy`
  classes deleted, all 625 lines replaced with imports of the real
  `Mock`/`Spy`/`Stub`/`CallRecorder`/`CallVerifier`/`VerifyCount`/
  `ArgMatcher`/`arg_*`/`matches_arg`/`mock_policy_*` from `std.spec.mock`.
  Every original test case's intent was ported. **Result: 41/41 passed.**
  - The old "matches arguments" case asserted `m.call("find_by_id",[123]) ==
    456` — that was testing a BUG in the fake (last-registered stub always
    won, ignoring the first arg-specific stub). The real `Mock` correctly
    keys stubs by `method:arg1:arg2:...` when `with_args()` is used, so the
    rewritten case now asserts the correct per-argument values (`123` then
    `456`).
  - The old "in_range()" case was marked pending with the comment "enum
    variant InRange(i64, i64) constructor broken — creates tuple instead of
    enum". That was describing the FAKE's own broken reimplementation
    (`InRange`), not the real module (`ArgMatcher.Range` via `arg_in_range`).
    Tested directly against the real API: **it works** — no gap, no new bug
    filed for this case.
  - Real `CallVerifier.verify()` is panic-on-mismatch and returns nothing
    (not a bool like the fake's `count_type`-based verifier), so each
    verification case now calls `.verify()` as the panic-gated assertion and
    separately asserts the underlying `recorder`/`get_matching_calls()`
    state, rather than comparing `.verify()`'s return to `true`.
- **`test/unit/std/mock_spec.spl`** (twin): the near-byte-identical
  duplicate (593 vs 625 lines, `diff` confirmed only cosmetic loop-shape
  differences, e.g. dict-literal `Stub.values` vs manual key/value list
  scan) was **replaced with a 4-case smoke test** that imports the same real
  `std.spec.mock` classes, instead of re-duplicating all 41 cases a second
  time. The full 41-case suite lives only in the canonical
  `test/unit/lib/common/mock_spec.spl` per this doc's own "consider
  deduplicating" unblock note. **Result: 4/4 passed.**
- No new gap bug docs were filed — every case ported cleanly against the
  real module, including the one case that looked like a candidate gap.
- Verified with `bin/simple test <path>` (per `.claude/rules/testing.md`),
  binary `bin/release/x86_64-unknown-linux-gnu/simple` (mtime
  2026-08-10 11:06:25 UTC; prints the Rust-seed WARNING banner per the
  known Stage-3 self-host blocker, `bin/simple --version`).

## Re-verified 2026-08-17 (worker s3_rust_other) — ALREADY-FIXED by content

Classified against current source, not SHA ancestry. The shadowing
reimplementation is gone: `test/unit/std/mock_spec.spl:20` now reads
`use std.spec.mock.{Mock, Spy, Stub, CallRecorder, CallVerifier}` and the file
is 1912 bytes (was 593 lines); `test/unit/lib/common/mock_spec.spl:14` likewise
imports from `std.spec.mock`. `grep` for a `class CallRecorder` / `class
CallVerifier` declaration in either twin returns nothing, so the real
`src/compiler_rust/lib/std/src/spec/mock.spl` is now the code under test.
Recommend CLOSE.

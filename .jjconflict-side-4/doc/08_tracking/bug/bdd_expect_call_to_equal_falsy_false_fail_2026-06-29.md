# Bug: `expect(<call>).to_equal(<falsy>)` false-fails in interpreter BDD runner

**Date:** 2026-06-29
**Severity:** High — likely a large share of the ~12k baseline test failures
**Component:** Rust seed BDD interpreter (`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`, `interpreter_method/mod.rs`)
**Status:** FIXED — commit 62cea5b6f5cb (seed rebuilt + deployed). Monotonic
`BDD_MATCHER_RAN` flag (bdd.rs + interpreter_method/mod.rs): a provisional
hollow-call failure stands only if NO matcher ran. Verified: `expect(falsy_call())
.to_equal/.to_be/.to_be_gte` pass; genuine mismatches still fail; bare
`expect(falsy_call())` no-matcher still fails (no false-green). lib/common sweep
fail rate dropped ~12% → ~3%.

## Minimal reproducer

```simple
use std.spec.*

describe "matcher zero/chain":
    it "chained len to_equal 0":        # FAILS
        val empty: [i64] = []
        expect(empty.len()).to_equal(0)
    it "intermediate var zero":         # passes
        val empty: [i64] = []
        val n = empty.len()
        expect(n).to_equal(0)
    it "literal zero":                  # passes
        expect(0).to_equal(0)
```

Result: `1 failure` — first `it` fails with:
`expected call result to be truthy, got 0`

## Root cause

`expect(<call-or-method-call expr>)` takes the general path in `bdd.rs` (~L851-874):
when the arg is `Expr::Call`/`Expr::MethodCall` and the evaluated value is falsy
(`0`/`false`/`""`/empty), it sets `BDD_EXPECT_PROVISIONAL = true` with the
"expected call result to be truthy" message. This provisional flag is meant to be
**cleared by a following `.to_*()` matcher** (`interpreter_method/mod.rs` L236-247
clears it for `to_equal`/`to_be`/...).

For `expect(<call>).to_equal(<falsy>)` the clear does **not** take effect, so at
example end (`bdd.rs` L693-695, `failed = hard_failed || provisional`) the test is
marked failed even though `to_equal` matched. Identifier/literal receivers never
set provisional, so they pass. Only **call/method-call receivers whose result is
falsy** are affected.

Dispatch divergence not yet pinned: there are 3 `to_equal` sites
(`interpreter_method/mod.rs:249`, `bdd.rs:1344` matcher-builder, driver
`execution.rs:1057`) plus the test-runner line rewriter
(`rewrite_method_expect_line`). The clear at `mod.rs:246` provably does not run for
this case — needs eprintln tracing + a seed rebuild to confirm which path runs.

## Impact

Direct per-file sweep of `test/01_unit/lib/common` (daemon-bulk-run is broken,
see below): ~172/746 specs FAIL (~23%, vs ~10% global baseline). Spot checks show
many are exactly this pattern — e.g. `crypto/hkdf_sha256_spec.spl`
(`expect(hkdf_expand_sha256(...).len()).to_equal(0)` for L=0 / L>255·hashlen, where
the library correctly returns `[]`), `compress/deflate_spec.spl`
(`round-trips empty input`). The library code is correct; the matcher is wrong.

## Workaround

Assign the call result to an intermediate `val` first:
`val n = call(); expect(n).to_equal(0)`. (Matches the existing language guidance
"chained methods broken — use intermediate var".)

## Related blocker — bulk runs (PARTIALLY fixed)

Bulk test runs (`bin/simple test <dir>` / full suite) false-failed with
`ERROR: test daemon unavailable; refusing direct test execution` (0/N) even with a
live `light_daemon.spl` — the client `test_daemon_ensure_responsive` ping cannot
reach the running daemon (stale-pidfile / IPC mismatch between the daemon_sdk ping
protocol and the file-based light_daemon).

**Fixed (commit e17778a6763c):** both runner mains
(`src/app/test_runner_new/test_runner_main.spl`,
`src/lib/nogc_sync_mut/test_runner/test_runner_main.spl`) now fall back to direct
execution instead of refusing 0/N (mirrors `test_runner_client.spl`).

**STILL BROKEN downstream:** with the fallback, a directory run reaches
`Session setup: ~5000ms` then exits silently — no per-file output, no Results
summary, `test_result.md` not updated. Halt is in the per-file path
`run_single_test` → `run_test_file_interpreter` on the FIRST file (sequential AND
parallel both halt there). NOT the self-protection governor (needs both CPU>limit
AND mem>limit; host had ~62% CPU free / 119GB RAM free, no shutdown reason printed).
Single-FILE `bin/simple test <one_spec.spl>` runs in-process and works fine; only
the multi-file loop's per-file delegation halts. Root cause not yet found — needs
tracing inside `run_test_file_interpreter`. Until fixed, sweep via per-file loop.

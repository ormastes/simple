# Bug: alpha mode is NOT fail-closed — logs diff and returns empty, does not abort

**ID:** alpha_mode_not_fail_closed_2026-06-15
**Filed:** 2026-06-15
**Status:** RESOLVED 2026-06-16
**Severity:** P1 — security contract violation (name promises halt; impl only logs)
**Component:** src/os/crypto/dual_backend.spl

## Resolution (2026-06-16)

`_dual_backend_alpha_halt` now calls `rt_exit(70)` (EX_SOFTWARE) after logging,
so a genuine runtime/pure mismatch aborts the process — true fail-closed. Because
all four comparison paths (`dual_backend_choose_bytes/bool/u64/text`) route their
alpha mismatch through this one function, the fix covers every type uniformly; the
`return []/false/0/""` lines after the halt are now unreachable but kept for the
type checker.

The fix is deliberately narrow: it only fires on a TRUE mismatch (both backends
produced output and they differ). The one-side-empty *absent-oracle degradation*
in `dual_backend_choose_bytes` (lines ~187-190) is preserved — many alpha callers
have no real runtime oracle (e.g. the typed hash layer) and rely on degrading to
the present side rather than aborting.

Verification:
- `rt_exit` confirmed to halt under the seed interpreter (probe → `rc=42`).
- True alpha mismatch out-of-process → process exits `70`, execution does not
  continue past the mismatch (the test runner spawns one child process per spec
  file, so this cannot be asserted in-process without crashing the file).
- In-process specs restructured to assert alpha AGREEMENT (no halt) + the
  absent-oracle degradation path + BETA-mode mismatch (logs, returns preferred):
  `test/01_unit/lib/common/crypto/typed/seam_spec.spl` (4 pass),
  `test/01_unit/os/crypto/dual_backend_alpha_spec.spl` (4 pass, rewritten).

## Summary

`dual_backend_choose_bytes` in Alpha mode on a runtime/pure mismatch calls
`_dual_backend_alpha_halt(report)` — which is named "halt" — but the implementation
only does `serial_println(...)` then returns. It does NOT abort, panic, or stop
execution. Control returns to the caller, which receives `[]` (empty byte slice).

The plan's contract (`doc/03_plan/lib/crypto/custom_type_alpha_crypto_team_plan_2026-06-15.md`)
states alpha = "fail-closed on mismatch". Logging and returning empty is NOT
fail-closed; it is fail-silent with a misnamed function.

## Evidence

From `src/os/crypto/dual_backend.spl` (lines ~167, ~198-199):

```simple
fn _dual_backend_alpha_halt(report: text):
    serial_println("[dual-backend] " + report)
    # NO abort/panic/halt here — execution continues

fn dual_backend_choose_bytes(...) -> [u8]:
    ...
    if config.mode == DualBackendMode.Alpha:
        _dual_backend_alpha_halt(report)
        return []          # caller receives empty, not a halt
```

## Demonstrated by seam spec

`test/01_unit/lib/common/crypto/typed/seam_spec.spl` proves execution continues past
mismatch (the `expect` after `alpha_run_span` runs and the result is empty, not a crash):

```simple
it "mismatch: two closures returning different ByteSpans yield empty":
    val a: [u8] = [1u8, 2u8, 3u8]
    val b: [u8] = [4u8, 5u8, 6u8]
    val s = alpha_run_span("test", "mismatch", fn(): ByteSpan.new(a), fn(): ByteSpan.new(b))
    expect(s.len()).to_equal(0)   # passes — alpha returned [], did not abort
```

## Security risk

Two scenarios where fail-open matters:
1. A MAL input triggers both backends to return the same wrong value (both compromised)
   — alpha can't detect that, but that is out of scope.
2. A bug causes one backend to return empty `[]`. The other returns a valid tag.
   Alpha fires, logs, and returns `[]`. The caller may treat `[]` as "no result" and
   silently succeed rather than reject, depending on callsite error handling.

Additionally, if both backends erroneously produce `[]`, `dual_backend_bytes_equal([], [])`
returns `true` and alpha will NOT fire — a matching-empty false-positive.

## Proposed fix

`_dual_backend_alpha_halt` should either:
- Call a process-abort extern (e.g., `rt_abort()`), or
- Return a `Result`/signal that the callsite can propagate as a hard error.

Until fixed, all callers relying on alpha for security-critical paths must add their
own mismatch checks after calling `dual_backend_run_bytes`.

# Discovery omissions are reported as executed test failures

Status: reproduced in the coherent source cut; private summary repair is not
fully qualified. Bug-database reconciliation is pending. No native or whole-suite
success is claimed.

The canonical cold discovery driver retained 19,111 original file paths and
eight unavailable alias inputs with explicit NOT_RUN records. Those eight inputs
executed zero cases. Its aggregate text nevertheless printed eight total and
eight failed tests. Listing inputs is not executing their test bodies.

The affected owner is
`src/lib/nogc_sync_mut/test_runner/test_runner_output.spl`. Its
`aggregate_failed_count` deliberately preserves a nonzero failure indicator for
unverified file units. However, `run_aborted_before_execution` recognizes only
an empty result-file array. Retaining the omission evidence defeats that guard
and makes the aggregate indicator look like an executed-case count.

Keep the named omission records, nonzero exit and original evidence. A proposed
private correction also recognizes a result containing only NOT_RUN files and
zero example counters as an abort before execution. It prints the number of
unrun file units without presenting them as assertion failures. Mixed executed
and omitted results still require a separate review of case-versus-file totals;
this proposal does not claim to solve all summary accounting.

## Bounded source evidence

The exact production owner and dependencies were copied from the authenticated
cold candidate closure. The first diagnostic could not load the canonical
single-file runner; its absent entry was supplied from an independently pinned
original source closure, without replacement libraries or stubs. The subsequent
baseline executed the real reproducer: one case, zero passed, one failed.

The private candidate executed seven cases, with six passed and one failed.
The first case reached the new abort guard, zero-case counters and non-success
assertions, then failed because the authored test incorrectly expected exit 6.
The canonical classifier returns Unverified/exit 5 for NOT_RUN; BlockedScenario
uses exit 6. A corrected fixture is retained but has not been run. Do not report
the candidate as a seven-case pass or promote its source patch.

Both real source runs traced 149 confined reads with unchanged source pins and
final Windows Job count zero. No fourth retry was performed. Six prevention
cases covered mixed executed/omitted inputs, assertion failures, contradictory
class tokens, feature-gated skips, empty selections/preflight failures and
silent zero-example children. No native behavior or performance was measured.

Retained immutable receipts, logs, source pins, original fixtures and the
corrected-but-unrun fixture are under
`build/native_probe/not-run-summary-20261013-root/`. Its `QUALIFICATION.json`
records the outstanding failure and explicit source-promotion hold.

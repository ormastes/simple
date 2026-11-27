# Native runner plain-source and source-doctest routing

Status: source routing fixed and qualified with the retained compiler; no compiler
rebuild or deployment. Canonical bug DB reconciliation remains pending.

Before this change, an explicitly requested source doctest also entered the
ordinary spec lane. Comment/docstring-only files failed for having no main or
top-level statements, even when their documentation examples passed. Plain SPL
top-level assertion snippets executed but were rejected for lacking BDD evidence.
Do not solve this by treating a child exit zero as a test pass.

## Bounded semantics

The existing compiler lexer supplies code-only facts; the existing SPipe source
partitioner separates imports, declarations and top-level executable statements.
For a non-`_spec.spl` source without BDD structure, a nonempty executable body is
wrapped in one real `describe`/`it` example. Imports and declarations are retained.
A private exclusive sibling file preserves import resolution. Its child must
produce structured BDD evidence, consumed regardless of the ambient assertion
flag. Setup, mismatched child arguments, cleanup and environment failures return
errors. Early `exit(0)` and a printed fake summary cannot qualify the snippet.

Empty/comment/string/declaration-only/pass-only bodies do not acquire generated
examples. Main-only application modules are outside this top-level snippet
contract. Existing BDD sources and `_spec.spl` files retain strict no-example
handling. An explicit single `.spl --spl-doctest` target runs only documentation
unless real BDD structure is present. Mixed BDD/documentation sources keep both
lanes. Directory, `--all` and `--whole` discovery remains combined.

## Verification

The native source-classification probe passes all nine named cases. Production
source identity: `7d59a2c5561`; only regression scripts/fixtures and this report
changed afterward. Retained phase2 producer SHA256:
`0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`.
Runner SHA256: `bc2eecb9edcae539e7f4a3328ceff47152cda1ebd8a6e13e7545a23c3773c6be`.
Build: 203.487 seconds, peak observed tree RSS 7,511,952 KiB, quiescent completion.

All 32 actual acceptance invocations have the expected exits. BDD, SSpec,
Markdown, plain top-level SPL and all four source-documentation formats have
positive/negative/empty controls. Mixed BDD+docs passes only when both pass;
BDD-only failure and docs-only failure remain failures. Declaration-only and
string-only files fail. The early-exit and fake-summary controls return
`structured BDD evidence unavailable`; plain positive runs one genuine example.
The native runner uses the retained Phase1 child: this is mixed-producer
qualification, not phase2 child admission.

Commands:
- `sh scripts/check/check-native-source-routes.shs --binary <native-probe>`
- `sh scripts/check/check-test-runner-source-routes.shs --runner <native-runner> --child <pinned-child> --out <new-receipt-directory>`

Both gates are explicitly manual because ordinary CI lacks their producer-bound
executables. The actual-run gate verifies exact expected exits, counters and
negative causes. Its `--verify-existing` mode behaviorally re-evaluates trusted
local receipts, pins executable and fixture digests, and gathers missing full
failure diagnostics; it is not a tamper-evident receipt protocol.

## Diagnostics and retained limits

The original console-error assertion rejected five negative source-doctest rows:
`_dt_failure_reason` selected an engine-demotion line before the actual panic.
Four native private-worker SDN diagnostics expose full BlockResult stderr and
prove the expected panic. The mixed BDD+doc private worker instead panics while
serializing SDN (`RTS` followed by byte 1), after correct text verdicts. That
separate SDN failure is retained and unqualified, not bypassed or claimed fixed.
The exact mixed same-file doctest composite was then executed with the same
pinned child: stderr proves `error: semantic: panic: CALIBRATION_EXPECTED_comment_red`,
exit 1. The original native runner still owns the mixed acceptance verdict;
the diagnostic supplies only the hidden failure cause. Its spec lane reports
one pass and its doc lane reports one failure.

Receipts: `/tmp/runner-source-routes-evidence-20261028/`, including
`probe-check.stdout`, `runner-build.status`, `runner-build.rss.env`,
`qualification/rows.sdn` (original five diagnostic-check failures),
`qualification-verified.stdout` (one remaining mixed diagnostic check), and
`qualification-verified-final.stdout` plus `qualification/rows.verified.sdn`
(final 32 cases, zero failures). Full negative diagnostics and exact mixed
composite bytes are retained in `qualification/`. Successful green invocations
were not repeated merely to improve their receipts.

Luna reviewed source routing, receipt requirements and cleanup. Remaining
MC/DC fallback diagnostics and native SDN transport/serialization are not
qualified by this change. No deployed binary was replaced.

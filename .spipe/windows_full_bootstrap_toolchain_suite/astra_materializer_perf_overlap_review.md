**Consumer defect confirmed; reported runtime remains unverified.** HEAD `c509fecf23ba5a1046474cbf0cbf7dda5eda734a` contains 116 aliases. HEAD blobs establish `src/compiler/types → 30.types` and `test/03_system/feature/lib/compiler → ../../../../src/compiler`. Both legitimate targets trigger [authority.shs:3284](C:/Users/ormas/dev/simple/scripts/check/lib/bootstrap-stage3/authority.shs:3284). Equal targets are also rejected.

I found no retained timing log establishing 15 minutes or 90/116. [state.md:106](C:/Users/ormas/dev/simple/.spipe/windows_full_bootstrap_toolchain_suite/state.md:106) instead records actual-116 as blocked; lines 104–105 record synthetic PASS. Treat the supplied timeout account as uncorroborated, not completed materialization.

**Minimal implementation sequence:**

1. Add topology regression fixtures; replace target-target prohibition with component-aware alias checks.
2. Run one long-lived native helper, compiling once. Currently [producer:757](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:757) starts PowerShell per action; [metadata:205](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:205) starts it twice. Batch blob validation, target inspection, identity and receipt encoding.
3. Capture one HEAD tree; retrieve unique blobs through bounded `cat-file --batch`. Cache immutable blobs by object ID and policy bytes/hash per invocation. Replace producer per-row Git and [consumer:3062](C:/Users/ormas/dev/simple/scripts/check/lib/bootstrap-stage3/authority.shs:3062) launches. Recheck HEAD and policy before publication.
4. Keep mutations serial. Consider two metadata workers only after measurement, with deterministic records, bounded queues, shared handle ownership and cancellation.

**Overlap policy:** permit equal/nested canonical targets; sharing a target is not duplicate ownership. Reject duplicate alias rows, case/component collisions and ancestor/descendant alias paths. Reject targets equal to or beneath any alias. A target may contain aliases—`src/compiler` does—but enumeration must prune those leaves; never follow them recursively. Reject expansion cycles, external/device paths and unexpected reparse ancestors/leaves.

Correct junctions should remain `already`. Current [producer:354](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:354) rejects directory symlinks by tag. Accept verified directory symlinks unchanged only through an explicit producer/consumer contract extension; conversion requires approved materialization.

**Focused tests:** extend the [three-alias integration fixture](C:/Users/ormas/dev/simple/test/02_integration/bootstrap_stage3_git_state_materialized_test.shs:30):

- Accept compiler/types nested targets, two aliases sharing one target, and `x` versus `xy`.
- Reject duplicate alias ownership, nested aliases, self/two-node cycles, target-through-alias traversal, case collisions, escapes and unknown reparses.
- Verify correct junction/symlink identity remains unchanged; wrong targets fail.
- Inject target/ancestor replacement, pending appearance, HEAD/policy drift, helper death and destination collision; require preserved user bytes and no success receipt.

Preserve [held-target revalidation and atomic publication](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:671), strict schema/counts, pending revalidation and directory SHA `-`.

**Proposed actual-116 oracle:** approved disposable checkout, one warm measured run; producer `<300s`, consumer within existing 28s/30s bounds. Record monotonic phase times, last row, exit/deadline, child counts, peak RSS/handles, HEAD/tool/policy hashes and receipt digest. Require 116 unique rows, zero failures, exact count equation, independent identity verification and consumer acceptance. Put telemetry outside strict v2 headers.

Risks: stale caches, prolonged locks, hardlink replacement semantics, symlink-contract compatibility. Nothing edited or executed beyond read-only inspection; unrelated changes preserved.
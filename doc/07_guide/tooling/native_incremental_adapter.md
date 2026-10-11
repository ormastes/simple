# Incremental restricted native adapter

This temporary bridge extends the proven one-file adapter to reviewed exact
source files. The initial catalog covers interpreter while scope, logical
short circuit, and mixed numeric arithmetic. It is not a general BDD compiler
and does not grant formal aggregate or standard-library framework authority.

The generator accepts a canonical subsystem inventory and an ordered prefix.
The first prefix contains one file; each subsequent manifest must append
a nonempty batch of canonical owners without changing earlier order. Source bytes must
match both the canonical inventory and the reviewed catalog. Every supported
case is translated, with authored body lines preserved and actual/expected
scalar expressions each evaluated exactly once. A negative variant changes
only the first expectation in the first supported newly attached file. The short-circuit
expressions retain their division-by-zero right sides intact.

An unsupported file remains **detached**, with its verbatim original source,
hash and specific adapter rejection reason in the manifest. Its case and
assertion counts remain unknown. It is never counted as attached, compiled,
executed, quarantined assertion, or PASS. A detached-only addition has no
negative native gate and cannot be passed to the native runner. This is an
honest incomplete attachment record, not a substitute for importing that file
through the repaired normal test framework. No original test is commented out.

Generate prefix evidence using absolute paths:

```sh
perl scripts/bootstrap/native-incremental-adapter.pl \
  "$WORKSPACE" "$CANONICAL_INVENTORY" "$ORDERED_PREFIX" interpreter \
  "$NEW_PREFIX_EVIDENCE" "$PREVIOUS_MANIFEST"
```

For the initial one-file manifest only, use `-` as the previous manifest. This
generation step alone records zero compiled and executed owners. When migrating
from the proven one-file adapter, generate that initial manifest without
recompiling or rerunning its already green assertions.

Build the new cumulative entry and both controls:

```sh
sh scripts/bootstrap/run-native-incremental-adapter.shs \
  "$WORKSPACE" "$ADMITTED_COMPILER" llvm "$NEW_PREFIX_EVIDENCE" \
  "$STABLE_LANE_DIRECTORY" "$PREVIOUS_GREEN_RESULT"
```

The previous green result must be either the canonical one-file adapter gate
receipt or a prior restricted prefix gate whose proven attached source owners
match. Merely generating the preceding manifest is insufficient. For Cranelift,
replace `llvm` and use its own physical workspace, lane and receipt. The runner
validates admission and the frozen runtime capsule. Native builds keep no-stub
fallback, cold source inventory initialization, HIR cache disabled, 6,835,937 KiB
enforced RSS and 1,800 second deadlines. `NATIVE_ADAPTER_THREADS` and
`NATIVE_ADAPTER_OBSERVATION_BUDGET_MS` select positive resource bounds (defaults
10 and 5000); these settings are recorded in the immutable build receipt. Runtime execution uses the bound workspace as its working directory.

Each lane owns one stable entry location, latest positive/negative binary pair,
and backend/producer/workspace-bound cache. A writer lock excludes simultaneous
lane builds. Old prefixes retain compact execution logs, hashes and source
evidence and immutable positive/negative executable copies; the lane binaries are replaced only when advancing. The verifier
checks the live binaries against the current receipt, so a historical receipt
cannot be reverified as if the mutable latest binary still matched it. Never
share the workspace or cache with another lane or relocate native caches.

`result.json` records `RESTRICTED_PREFIX_GATE_PASS`, attached/compiled/executed
and detached counts, every case/assertion, both exact exit statuses, and
`formal_product_pass: false`. It is written only after both actual executions
and transcript checks succeed. Generated manifests remain explicitly separate
from these execution results. Failed build logs and cache are retained.

The current prefix source snapshots are suitable for the initial small bridge;
do not run thousands of cumulative snapshots through this wrapper. Full-group
attachment needs the normal framework and a shared immutable source store,
not repeated source copies or a fabricated full-inventory PASS.

Focused generator regression:

```sh
perl scripts/bootstrap/tests/native-incremental-adapter-test.pl
```

## Batch probes and verified survivor unions

`scripts/bootstrap/native-batch-bisect.pl` coordinates immutable selections
around a verified native starter. It does not compile tests or grant support
for unsupported syntax. Use the complete ordered inventory and set batch size
to the remaining owner count to try the whole remainder first.

```sh
perl scripts/bootstrap/native-batch-bisect.pl init "$SOURCE" "$CANONICAL" "$ORDERED" interpreter "$REMAINING" "$NEW_STATE" "$STARTER_RESULT" llvm "$REVIEWED_NATIVE_AUTHORITY"
perl scripts/bootstrap/native-batch-bisect.pl next "$NEW_STATE"
perl scripts/bootstrap/native-batch-bisect.pl record "$NEW_STATE" "$OUTCOME_JSON"
```

The v2 controller distinguishes two operations:

- A **probe** builds a new subset with its original proven baseline. Failed
  probes split only the added files. A singleton probe failure retains the
  original file, diagnostics, a separate `assert(false)` marker and SKIP ledger.
- A **merge** builds independently passing files with the latest accepted
  survivors. The new files count as accepted only after this cumulative union
  passes. Failed unions split their new candidates. A singleton union failure
  records the full interaction without declaring one file the sole cause;
  unrelated pending batches continue.

For example, when A,B,C,D fails, A,B fails, A passes, B fails, and C,D passes
against the original baseline, the next request is A,C,D with the baseline.
C,D are not discarded or counted accepted before that union executes. The old
flat complementary-half controller could lose this progress; v1 states require
migration and are not accepted by v2.

Exact prior selection decisions are reused through their immutable outcome
hashes, without rerunning native work. Failure reuse additionally checks the
original diagnostic hash. Accepted unions always refer to a native result;
manifest-only attachment never counts as compilation or execution. Infrastructure
and unsupported-adapter failures are BLOCKED and do not become failed assertions.
Quarantine currently excludes a whole file. Reattaching a file with a particular
assertion commented requires a separately reviewed case/line ledger and an
actual native rerun; that operation is not implemented by this coordinator.

## Native authority and backend isolation

The initial migration requires an explicit reviewed authority file, schema
`simple-reviewed-native-authority-v1`, containing backend, compiler path/SHA-256,
starter result SHA-256, positive/negative binary paths/SHA-256, `reviewed_by`, and
review evidence path/SHA-256. This is needed because older starter receipts do
not consistently contain a backend binding. A supplied backend label alone is
insufficient; the migration mapping must be reviewed against retained build
commands and artifacts. The controller verifies the mapped ELF artifacts and
hashes but cannot independently establish the human review's correctness.

Every subsequent PASS binds `build.env` backend, compiler SHA, workspace and
manifest hash, plus both retained ELF hashes, to the strict native result. LLVM
receipts cannot satisfy Cranelift state. Both backends may receive the same
canonical source/problem list, but their native outcomes remain independent.
Currently the strict result validator admits only the restricted prefix schema.
A normal-framework validator must be reviewed against real canonical registry
ledgers before this coordinator can admit full-group results. It must not be
bypassed by generating a synthetic restricted receipt.

Changed-behavior regressions:

```sh
perl scripts/bootstrap/tests/native-batch-union-test.pl
perl scripts/bootstrap/tests/native-batch-union-cli-test.pl
```

These tests use explicit coordinator fixtures, not native product evidence.
They cover the nested survivor counterexample, independently failing-file
combinations, failed unions, exact-decision reuse, independent backend authority,
and stale diagnostic rejection.

## Evidence preservation

The runner records the writer PID and terminal phase/exit on ordinary exits and signals. SIGKILL cannot write a receipt; absence remains interrupted with unknown outcome. An existing build, result, or terminal receipt is rejected before installing the receipt-writing trap, preserving prior evidence.

The ELF check declares its header buffer before reading it. The earlier expression-scoped declaration rejected a valid native executable. The historical recovery script remains with its evidence; the supported runner provides no general resume bypass.

Batch isolation is coordinated separately. The same selected problem source files must be exercised on LLVM and Cranelift, with backend-specific outcomes. Shared infrastructure failures are not assertion failures, and excluded assertions never count as passing coverage.

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
also requires the preceding `build.env` to match the current workspace, compiler
SHA-256, backend and frozen runtime-capsule receipt SHA-256. Prefix results
hash-bind that build receipt and repeat those identities; missing or altered
bindings fail before compilation. Legacy
one-file migration requires its original matching build receipt. Older prefix
results without a build binding require a fresh evidence attempt; they are not
silently upgraded into producer-bound evidence. New build receipts retain the
previous build receipt hash as well as the previous result hash. These local
hash bindings detect mixed evidence, not maliciously rewritten receipt chains.
The runner
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

## Evidence preservation

The runner records the writer PID and terminal phase/exit on ordinary exits and signals. SIGKILL cannot write a receipt; absence remains interrupted with unknown outcome. An existing build, result, or terminal receipt is rejected before installing the receipt-writing trap, preserving prior evidence.

The ELF check declares its header buffer before reading it. The earlier expression-scoped declaration rejected a valid native executable. The historical recovery script remains with its evidence; the supported runner provides no general resume bypass.

Batch isolation is coordinated separately. The same selected problem source files must be exercised on LLVM and Cranelift, with backend-specific outcomes. Shared infrastructure failures are not assertion failures, and excluded assertions never count as passing coverage.

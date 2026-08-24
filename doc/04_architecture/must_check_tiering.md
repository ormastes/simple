# Mandatory Check Tiering Architecture

The registry (`config/check/must_check_gates.sdn`) is policy. The bootstrap
runner is the sole evidence producer. The textual ledger
(`doc/08_tracking/check/must_check_db.sdn`) is retained state. The push runner is
a read-only consumer of the ledger and committed Git trees.

Trust flows in one direction:

`bootstrap phase artifacts -> per-phase verifiers -> automated gates + retained logs -> atomic SDN ledger -> push`

The push consumer recomputes a content fingerprint excluding the ledger itself,
requires one-to-one unique registry/result IDs and exact command agreement,
retains a per-gate PASS time, and verifies each PASS evidence file against its
recorded SHA-256. The canonical all-TODO `unrecorded` ledger is the sole
pre-promotion state: when its pushed predecessor is also unpromoted, bootstrap
debt is reported and every bounded structural gate still runs. A predecessor
with genuine promoted evidence permanently closes that exception, preventing a
downgrade to `unrecorded`. Promoted state fails closed on malformed, stale,
failed, missing, tampered, evidence-less, or non-passing push-blocking rows.
Non-blocking TODOs remain visible. Push-tier commands are registry rows dispatched through a
closed ID/mode/command allowlist, so a changed manifest cannot turn the hook
into an arbitrary shell-command executor.
The quick rules evaluator separately binds the committed `rules.sdl` blob to a
reviewed digest in its checker. A policy edit therefore requires a matching
checker review; committed `cmd:` text cannot change independently and execute.
The push consumer also owns a minimum required bootstrap-ID ratchet. Manifest
and ledger may add gates together, but deleting a required TODO from both files
does not make the obligation disappear.
The quick rules checker parses `rules.sdl` from the exact pushed revision, and
that policy file participates in the producer/consumer fingerprint; dirty or
concurrent working-tree command text is never executed.
The consumer resolves each repository-relative evidence path as a regular blob
in the exact pushed revision, never through the live worktree, and applies a
64 MiB aggregate byte budget before hashing. It deduplicates identical ref
updates and accepts at most two unique updates per invocation; larger pushes
fail closed with an instruction to split the push. These bounds prevent
committed policy input from turning the interactive hook into unbounded local
file I/O.
The bootstrap owner writes logs before the ledger under
`doc/08_tracking/check/evidence/<source-fingerprint>/` and records
repository-relative evidence references and hashes. Operators commit those
logs with the ledger, avoiding a circular Git hash dependency
while binding PASS evidence to the source/config/scripts/tests/docs it qualifies.
The producer refuses production recording if fingerprinted inputs differ from
`HEAD`. External or hardware TODO receipts use a separate explicit import:
their first PASS requires a regular committed blob at `HEAD`, and later source
fingerprints carry the PASS only while that exact blob/hash remains committed.
The external validator owns a shared signature/hash loader plus narrow
gate-specific semantic oracles. The RISC-V sharing oracle compares three
reviewed ownership attachments with the exhaustive committed HEAD path
universe and rejects missing bilateral or specialization rationale; it does not
promote runtime or board evidence.
Performance semantic oracles remain lane-specific rather than becoming a
configurable threshold engine. Binary-size parity loads the actual committed
stripped artifacts and recomputes identity, size, equivalence bindings, and the
comparison after common signature/hash validation.
Automated source-sensitive results still invalidate on fingerprint changes.
After Stage 1-4 admission succeeds, the bootstrap owner canonicalizes the exact
validated Stage 4 path and injects it as `SIMPLE_BINARY` and the established
`SIMPLE_BIN` compatibility name for every automated
gate. Ambient or deployed `SIMPLE_BINARY` values cannot redirect that evidence
to a stale compiler.
Detector mutation suites are bootstrap evidence, not per-push setup. The
runtime-API guard's push row therefore invokes `--scan-only` with an explicit
committed range, while a separate required bootstrap row runs `--selftest`.
The interpreter-extern registry and type-walk parity guards use the same split:
push executes only their source scan, while bootstrap owns mutation fixtures.
The normal standalone command keeps self-test-first behavior.
The exhaustive structural-tree fixture campaign is a bootstrap automated row.
Interactive push retains the same final-tree invariants but evaluates only each
bounded committed tip and its count-only first-parent reference.
Whole-tree semantic scans, compiler-dependent checks, C runtime compilation,
and executable parse probes are bootstrap producers even when their gate names
originated in the push hook. Retiering changes their execution owner, not their
authority: each becomes a required automated manifest/result pair whose PASS
log is fingerprinted and consumed by the next push.
Ledger schema v3 also binds every result to a non-empty owner. A non-passing
row must retain an actionable unblock condition; a passing row must use
`unblock_condition=none`. The push consumer rejects unowned work, vacuous TODOs,
and PASS rows that still claim unresolved work.

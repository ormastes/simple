# Bootstrap planner v1 unbound authorization

Status: RESOLVED-ON-THE-PRODUCTION-PATH 2026-09-02, **with one residual named
below — do not read this as "v1 is gone", because it is not.** Verified against
`origin/main` @ `1b76db1d6c3`.

### What was checked (2026-09-02)

**The defect is unreachable in production.** The only receipt the planner emits,
and the only one the bootstrap scripts verify, is v2:
`src/app/build/bootstrap_receipt_planner.spl:8` imports
`bootstrap_authorization_receipt_v2` / `bootstrap_sha256_is_canonical_v2` and
nothing else, validates all four admission hashes (`:14-20`), and builds the
receipt at `:77`. On the script side,
`/usr/bin/grep -rn "planner-admission-v2" scripts/` hits 10 files including
`bootstrap-from-scratch.sh:439`, `resume-stage3-from-admitted.sh:26`,
`resume-stage4-from-admitted.sh`,
`produce-bootstrap-planner-admission-v2.shs:279,284`,
`check-bootstrap-planner-admission-producer.shs` and
`verify-bootstrap-planner-admission-bound.shs`. No script consumes a v1 planner
receipt; the `*-admission-v1` strings that do exist in `scripts/`
(`simple-bootstrap-lineage-admission-v1`, `simple-bootstrap-stage2-admission-v1`,
`simpleos-executable-admission-v1`, …) are different schemas for different
subsystems, not this one.

### Residual — the v1 acceptor is still in the tree (was nearly missed)

An initial pass over `scripts/` alone concluded "v1 no longer exists". That was
wrong, and the correction is the useful part of this update:
`src/app/build/targets/bootstrap_policy.spl` still contains the whole v1
mechanism this record indicts —

- `:28` `bootstrap_authorization_receipt_v1(target, reason)`, admitting on the
  bare **prefix** test `target.starts_with("//bootstrap:") or
  target.starts_with("//release:")` plus a typed reason, binding nothing else;
- `:37` `bootstrap_authorization_error_v1(receipt, target)`, which returns `""`
  (i.e. ACCEPTED) for any such receipt.

It has no production caller — `/usr/bin/grep -rn` across `src/app/` and
`test/01_unit|02_integration` finds references only inside that file plus one
spec, `test/01_unit/app/build/bootstrap_policy_spec.spl:38`, which asserts the v1
acceptor returns `""`. So it is unused product code kept alive by its own test,
exactly the "prefix admission authorizes any target" surface v2 replaced.

**Not deleted here** — removing it means removing its spec too, which is a
scope call for the bootstrap-policy owner, not a triage pass. Recommended
follow-up: delete `bootstrap_authorization_receipt_v1` /
`bootstrap_authorization_error_v1` and their spec, per the repo rule against
leaving unused code, so a future caller cannot re-adopt the unbound path.

### Test status

No new regression test was written. The v1 acceptor already has one
(`bootstrap_policy_spec.spl:38`) and it passes — but it pins the WRONG
behaviour for this record's purposes (it asserts prefix admission succeeds).
The correct successor coverage is v2's structural binding, exercised by
`scripts/check/lib/bootstrap-planner-admission-bound.shs`. A meaningful new
test here would have to assert v1 is *unreachable*, which is a
census/lint-shaped check, and it should be written as part of the deletion
above rather than freezing the dead code in place.

Previously: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

The version-1 planner receipt authorized any target with a bootstrap or release
prefix and bound only a typed reason. It did not identify the admitted parent
compiler, its sanity/provenance evidence, frozen runtime, planner source
closure, git state, build command/environment, cache scope, planner executable,
planner smoke, or authorization artifact. A copied or stale receipt therefore
could not prove which inputs had been planned.

Planner admission v2 replaces prefix admission with the two exact targets
`//bootstrap:stage3` and `//bootstrap:stage4` and a target-specific reason set.
Its authorization content binds the parent compiler, runtime snapshot, source
closure, and planner hashes. The enclosing canonical receipt binds all frozen
evidence using unique ordered fields and exact lowercase SHA-256 values.
Canonical nonsymlink paths, mutation rejection, and runtime-plus-closure cache
scope are checked structurally by
`scripts/check/lib/bootstrap-planner-admission-bound.shs`. Structural validity is
not authority: the public verifier deliberately rejects every body until an
independently admitted Stage 2 parent can build and execute the planner under
an owned pre-exec lock and bind exact argv, environment, stdout, exit status,
derivation receipt, and smoke evidence. The unsafe shell body publisher was
removed.

Focused negative evidence is
`test/01_unit/scripts/bootstrap_planner_admission_bound_contract_test.shs`; the
pure-Simple source boundary is covered by
`test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl`.
Neither test builds or runs a planner. Operational closure still requires an
admitted parent, a built planner, a real smoke receipt, and a resulting v3
admission before any bootstrap stage starts.

## Planner admission v3 frozen contract

Version 2 is permanently legacy because hashes without their canonical
transcripts cannot be semantically replayed. Version 3 admits only an envelope
published by `scripts/check/produce-bootstrap-planner-admission.shs`, whose
canonical path and pre/post SHA-256 are bound. The producer requires an
independently verified Stage2 tuple: identical origin/admitted compiler hashes,
replayed sanity, canonical transcript/log, frozen runtime snapshots,
source/tool snapshots, and git state. Completed Stage3 provenance cannot be a
prerequisite because it is an output of the operation being authorized. The
producer freezes the parent tuple, runtime, source closure, git state, and a
fixed trusted-tool snapshot before creating any output.

The producer owns the output lock and a private sibling staging directory. Its
sealed evidence directory is read-only during child execution; build and smoke
children receive distinct bounded writable directories. Paths, arguments and
environment values containing line, tab, equals, carriage-return, or NUL
delimiters are rejected. Exact cwd, argv and allow-listed environment
transcripts are stored as canonical files and hash-bound, not represented only
by digests. Build and smoke each record their OS-observed child PID, exit
status, timeout status, stdout, stderr, combined log and hashes. Output is
size-bounded and a timeout is mandatory.

Positive completion requires exit zero and a newly created, regular,
non-symlink, non-empty executable whose post-build hash is bound after all
frozen authorities are rechecked. The canonical pure-Simple in-process
`native-build` path is silent on success; `Build complete: N compiled` and
`Linked ... via clang` are Rust-seed/fallback markers and MUST NOT be required
or accepted as positive proof. Build output must contain no fallback, stub,
TODO, unresolved-symbol, zero-output, Rust-seed build-completion, or
clang-link marker. Positive semantic proof instead comes from two isolated
planner smoke executions that reproduce the exact producer-derived
authorization leaf. The planner never authors the admission envelope.
Smoke is replayed in a fresh isolated directory with the same semantic argv,
environment and cwd and must produce the identical authorization while leaving
the candidate, producer, sealed evidence, and canonical destination unchanged.

Before execution the producer rejects non-canonical, symlinked, existing, or
out-of-root outputs. It rechecks all frozen identities and its own hash after
both children, publishes the complete evidence tree and ordered receipt by one
atomic sibling rename, and cleans staging and lock state on every signal or
failure. Partial publication and overwrite are forbidden. A future public
consumer must accept v3 only and replay every hash, transcript, semantic
authorization, terminal record, bound, containment and immutability assertion.
No v3 producer or consumer is implemented today. V1, v2,
orphan, fixture, fallback, partial and structurally forged receipts fail.

The boundary protects against accidental or child-process evidence mutation.
A hostile same-UID process can still chmod a 0500 directory; cryptographic
protection against that threat requires an external signing/credential owner
and is outside this local bootstrap evidence boundary.

## Restart12 non-circular producer attempt

Completed Stage3 provenance cannot authorize starting Stage3. The admissible
parent is instead an independently verified Stage2 tuple: identical
origin/admitted compiler hashes, replayed sanity, canonical transcript/log,
frozen runtime snapshots, source/tool snapshots, and git state. A three-cycle v3
producer/consumer draft implemented that shape and its consumer positive and
deliberate-red contracts passed. The producer's incomplete-tuple negative still
exited before emitting the canonical `incomplete-stage2-tuple` diagnostic, so
the reason guard was not reached. The entire draft was reverted at the cap; v2
therefore remains fail-closed. TODO666 retains the producer, atomic envelope,
consumer/bootstrap switch, reason guard, and deliberate-red closure as one
indivisible future lane.

## Lane J re-verification 2026-08-17 (classified by CONTENT, not SHA ancestry)

**Verdict: STILL-OPEN (same root cause as bootstrap_admission_v2_fail_closed_blocks_all_bootstraps_2026-08-17).**
`scripts/check/lib/bootstrap-planner-admission-bound.shs` still only validates STRUCTURE
(`bootstrap_planner_v2_verify_structure`) and never executes the planner, so authorization
remains unbound to argv/env/exit status. These two rows collapse into one missing artefact:
a non-circular planner-execution producer. Fixing either requires building it.

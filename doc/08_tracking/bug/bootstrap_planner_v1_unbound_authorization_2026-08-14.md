# Bootstrap planner v1 unbound authorization

Status: CLOSED — superseded by the canonical v2 producer (bug database closure: 2026-09-14).

## Current tracking status, source-inspected 2026-09-22

The current `bug_db.sdn` row closes this original v1 defect. The canonical
producer now exists at
`scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`; it verifies
the Stage2 parent evidence, builds and executes the planner, records canonical
argv/environment digests, rejects an untyped reason in a negative smoke, and
emits a v2 admission receipt. The public verifier in
`scripts/check/lib/bootstrap-planner-admission-bound.shs` delegates to the
bound verifier rather than the historical unconditional refusal.

The existing producer regression is
`scripts/check/check-bootstrap-planner-admission-producer.shs`. Its parent
compiler and planner are fixtures: a passing result does not establish a real
native planner build, full bootstrap completion, or implementation of the v3
design below. The legacy consumer regression is
`scripts/check/check-bootstrap-reason-receipt-guard.shs`.

### Windows re-verification limits (2026-09-22)

Baseline: `origin/main` at `e0dd873da1b`, isolated D: sparse worktree, Windows
x86_64 with MSYS2 shell tools. This update changes documentation only; no
compiler, codegen, runtime, CPU, or backend implementation changed.

- The producer gate was stopped after 325.60 seconds before any final verdict.
  Its execution location at termination was not captured or proven. Initial setup also
  exposed a missing `release/version.sdn` in the sparse checkout; that tracked
  authority was restored before the bounded attempt. No PASS is claimed.
- At termination, the largest observed Windows process peak working set among
  the six surviving owned shell/time processes was 12,689,408 bytes. This is
  **not** a complete process-tree peak: short-lived descendants were not
  sampled. A total peak RSS measurement remains unavailable.
- The legacy consumer guard failed after 51.05 seconds with
  `None receipt did not return the canonical diagnostic`. A direct diagnostic
  replay entered the default strategy supervisor and ended with
  `stage-engine-failed`, producing scheduler evidence before the expected
  receipt refusal. This is a current verification gap; it does not establish
  acceptance by `bootstrap_planner_v2_verify`. MSYS2 GNU time reported
  6,378,096 KiB max RSS for that run; its accounting was not validated and must
  not be treated as a reliable Windows working-set measurement.

Verification TODO: bound and profile the Windows producer gate through its
positive and negative fixtures, using process-tree memory sampling. Reconcile
the legacy consumer guard with the default strategy supervisor: separately
prove direct receipt-validation refusal and that ordinary bootstrap rejects
legacy receipts before stage execution. The historical Linux fixture pass in
the database is not fresh Windows, macOS, FreeBSD, alternate CPU, or native
codegen evidence. Do not infer a performance comparison from this documentation
change or mark these verification tasks complete from source inspection.

The sections below preserve the original investigation and proposed v3 design.
Statements that no v2 producer exists and the August STILL-OPEN verdict describe
the historical state; they are not the current implementation status.

## Historical report (2026-08-17)

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

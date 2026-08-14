# Bootstrap planner v1 unbound authorization

Status: OPEN — v3 design is frozen; non-circular producer cycle exhausted and reverted

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

Positive completion requires exit zero, a non-empty planner, the exact native
build completion marker with a positive compiled count, no fallback, stub,
TODO, unresolved-symbol, or zero-output marker, and an exact authorization leaf
derived by the producer. The planner never authors the admission envelope.
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

# Actual configured V6 Host route

Status: AUTHORED_NOT_RUN. The executable scenario requires a genuine configured
Windows Host service. Missing setup, service, native backend, or fixture fails;
there is no mock owner, skipped success, fabricated process, or scripted Docker.

The fixture is `C:\SimpleQualification\host-auth-route-v6.sdn`, containing exactly
six public text fields: `setupPath`, `setupDigest`, `hostDeploymentRoot`,
`hostAuthorityDigest`, `expectedScopeDigest`, and `expectedEnrollmentDigest`.
It contains no secret. Provision the private V6 setup with the actual OS entropy
producer under its protected parent, and start the real dedicated V6 Host mode
with the installed enrollment and single physical-scope writer. Do not run an
independent V5 instance against the same capacity. The expected digests must come
from the actual installed enrollment/configuration and current Host scope.

The scenario opens the protected reader, selects the immutable ready record,
performs the actual nonce challenge/request/reply exchange, consumes its one-use
verified result, and checks the real typed Host status against the fixture. It
attempts exchange cleanup before reader cleanup. Failed cleanup retains actual
owners in process-local fixture fields; this does not promise persistence after
the test process exits. All assertions occur after those cleanup attempts.

The following mandatory additional acceptance procedures remain NOT_RUN and
are not claimed as covered by this one status scenario:

- Dispatch a genuinely signed disposable workload through the actual Controller
  root and CLI; verify prepare/execute share one Host incarnation and exact
  retained journal, and inspect the actual created runtime through the common
  Container API. Preserve the exact execute archive and Controller/Host receipts.
- Interrupt the connection after an actual execute write, before the reply.
  Verify Unknown and retained cleanup; reopening may inspect the original digest
  but never resends execute automatically.
- Submit progress/cancel with another operation, scope, execute digest, or
  incarnation. Verify refusal before effects on the actual pending operation.
- Perform authenticated stop with the exact current scope/incarnation. Verify
  quiescing precedes Host close, pending obligations refuse stop, and a close
  failure never reopens normal dispatch. Reply success does not certify later
  socket/listener/reader cleanup.
- Restart using the same setup key and existing Host journal. Verify a new lease
  selects only its immutable ready record. A new lease without a ready record is
  unavailable, with no old-record fallback. Reader sharing that prevents lease
  replacement must preserve actual startup failure/quarantine, not retry it.
- Replace the selector while a stop reply drains. Verify delivery/verification
  Unknown, preserving confirmed internal Host-close facts and remaining owners;
  no reconnect/replay or stale-selector signing exception is allowed.
- Exercise failures at setup/read-root acquisition, publication uncertainty,
  ready readback, listener close, and reader close. Verify the actual returned
  cleanup carrier and original error survive CLI rendering and exit. In-process
  caps do not constitute durable post-exit recovery.

Interactive authenticated terminal binding remains a required later integration
through the same runtime owner. This transitional Host route does not implement
that user flow. Native timing, concurrency, restart liveness, power-loss behavior,
stock SSH, and production readiness remain unqualified.

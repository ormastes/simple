# BuildRunner source-session scenarios

Status: authored manual outline, **not_run**. This is not generated execution evidence. Source: `test/03_system/app/buildrunner/feature/scv_source_session_v1_spec.spl`. Generate/review the manual only during the authorized later Phase 3 verification.

The retention scenarios additionally exercise real durable authority files:

- Five independent authoritative metadata roots cause a fresh accounting-only
  preflight pressure refusal. The explicit `abort-capture` path is blocked by
  an actual held manager lock, then removes only its own unattached reservation;
  another capture owner and all independent nodes remain unchanged. Repeating
  the explicit command is idempotent.
- A real admitted snapshot's app records block abort. Removing those records
  still cannot bypass the store's independent active/durable pin and lease check.
- A mismatched declared input rejects source binding after real pin admission
  but before any source record or journal exists. Abort and retire both refuse
  the attached, unproven state; replaying the exact original inputs completes
  initialization without changing the retained source revision.
- Unknown state entries, a searchable but unreadable directory, and a missing
  state directory refuse abort without changing authority. The permission case
  requires a non-root POSIX user.
- Missing physical source makes real acquisition fail after reservation.
  Corrupting real retained source makes reopen fail after reservation. Neither
  path drops protection just because no session value is returned.
- The source-only context profile receives active and durable pins plus a
  reader lease. Reopen and scheduler retry keep the exact owner. Explicit
  reader-release API coverage leaves the durable dependent pin and source bytes.
- Real manager cancellation before dispatch returns 130, retains reader roots,
  and cannot retire either with its cancellation request present or with its
  still-pending journal after that request is removed. No child/reap proof is
  claimed by this scenario.
- An existing retirement marker blocks opt-in and omitted-option reopen before
  any source read, including a deliberately malformed marker.

Positive worker settlement and retirement require the separate actual-worker
integration manual at `doc/06_spec/02_integration/app/buildrunner/scv_retention_lifecycle_v2_spec.md`.

The source replay scenario creates an isolated real Git checkout with one Simple source and a digest-bound worker context. It calls the actual compiler source authority and V1 adapter through the production session opener, verifies the captured bytes, advances the inventory's CURRENT pointer, then reopens the saved session. Assertions require the original snapshot, exact record payload and raw pointer, plus an exact source revalidation for the requested task and scheduler retry. No worker or compiler executes.

The subject refusal scenario captures a real session, then attempts recovery without the explicit mode, with a changed plan and with a changed toolchain task identity. It also tampers with the source-only metadata to claim artifact authorization. Assertions require refusal at each boundary.

Separate unit specs exercise strict argv/role/argument grammar and raw-versus-tagged inventory record round-trip, and the actual transport copy loop with a nonspawning process port. The transport cases assert frozen versus edited-live source bytes, ordinary-input provenance, staged producer digest, frozen-source tamper refusal before spawn, invalid selectors and unchanged legacy selection. They do not establish OS process/sandbox/runtime behavior.

Runtime prerequisites: admitted pure-Simple runner; `SIMPLE_LIB=src`; no inherited SCV/source-root overrides; isolated caches/output; actual source revision and executable provenance captured. Native compilation, warm hit/miss counters, retained-output tampering, complete CLI resume/verify command scenarios, semantic provider admission and performance remain unexecuted Phase 3 gates.

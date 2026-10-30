# BuildRunner source-session scenarios

Status: authored manual outline, **not_run**. This is not generated execution evidence. Source: `test/03_system/app/buildrunner/feature/scv_source_session_v1_spec.spl`. Generate/review the manual only during the authorized later Phase 3 verification.

The first scenario creates an isolated real Git checkout with one Simple source and a digest-bound worker context. It calls the actual compiler source authority and V1 adapter through the production session opener, verifies the captured bytes, advances the inventory's CURRENT pointer, then reopens the saved session. Assertions require the original snapshot, exact record payload and raw pointer, plus an exact source revalidation for the requested task and scheduler retry. No worker or compiler executes.

The second scenario captures a real session, then attempts recovery without the explicit mode, with a changed plan and with a changed toolchain task identity. It also tampers with the source-only metadata to claim artifact authorization. Assertions require refusal at each boundary.

Separate unit specs exercise strict argv/role/argument grammar and raw-versus-tagged inventory record round-trip, and the actual transport copy loop with a nonspawning process port. The transport cases assert frozen versus edited-live source bytes, ordinary-input provenance, staged producer digest, frozen-source tamper refusal before spawn, invalid selectors and unchanged legacy selection. They do not establish OS process/sandbox/runtime behavior.

Runtime prerequisites: admitted pure-Simple runner; `SIMPLE_LIB=src`; no inherited SCV/source-root overrides; isolated caches/output; actual source revision and executable provenance captured. Native compilation, warm hit/miss counters, retained-output tampering, complete CLI resume/verify command scenarios, semantic provider admission and performance remain unexecuted Phase 3 gates.

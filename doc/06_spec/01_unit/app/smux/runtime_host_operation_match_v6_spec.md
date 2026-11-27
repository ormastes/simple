# Exact Host operation correlation V6

Source: `test/01_unit/app/smux/runtime_host_operation_match_v6_spec.spl`.
Status: **AUTHORED NOT_RUN**. No parser, runtime, native, service or cancellation
execution was performed.

Four cases invoke the actual pure matcher used by the canonical owner. They
cover exact progress/cancel identity, changed active operation or execute
digest, stale service incarnation or scope, and wrong action/payload refusal.
The input values are metadata, not fabricated native owners or signed grants.

The owner consumer performs its native caller-origin guard, computes scope from
the actual retained Host domain, compares its private execution tuple, and
invokes cancellation in that same turn. These pure cases do not qualify that
native call or cleanup. An actual configured-service test must demonstrate
wrong-operation refusal while another real operation remains active, exact
cancellation after launch expiry, retained pending cleanup and unchanged
immutable execution identity. Those native procedures remain **NOT_RUN**.

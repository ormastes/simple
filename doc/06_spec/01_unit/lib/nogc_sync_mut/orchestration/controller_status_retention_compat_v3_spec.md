# Optional retention status field — authored manual

Status: NOT_RUN / NOT_GENERATED / NOT_QUALIFIED, 2026-11-15.

Source: [controller_status_retention_compat_v3_spec.spl](../../../../../../test/01_unit/lib/nogc_sync_mut/orchestration/controller_status_retention_compat_v3_spec.spl).
These are pure structural checker assertions. The typed context/request values
are not admitted capabilities or authenticated native/dispatch authority. The
actual admission path still requires its independent protected authorization.

| Scenario | Required observation | Evidence |
| --- | --- | --- |
| Old and new bounded response | Existing status remains valid; the only new optional nested diagnostic also parses within revised bounds | NOT_RUN |
| Existing rejection boundaries | Unrelated fields still reject, and a diagnostic cannot hide an authority mismatch | NOT_RUN |

The optional field is ignored for admission and never confers retention/GC
eligibility. Runtime/interface/ABI, service transport, native Windows and platform
qualification remain NOT_RUN. This manual is authored, not generated or accepted
as SPipe execution evidence.

# Explicit control deadline specification

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_control_deadline_v1_spec.spl`.

Manual source mirror: seven authored cases, UNEXECUTED. Actual common API dispatch uses explicit managed scripted providers; no native cleanup evidence is claimed.

| Case | Assertion |
|---|---|
| Exact stop/destroy | Independent absolute argv, five create/entry/final clock samples and unchanged operation timeout. |
| Expiry crossing | Entry admits, final sample equals expiry, queued cleanup stays unconsumed and intent stays created. |
| Invalid context | Wrong action/digest/original operation and unknown control action reject before another executor attempt. |
| Clock failure | Zero/negative/exhausted entry or final samples cannot consume cleanup. |
| Cached result | Wrong context and expired context cannot obtain idempotent stopped success. |
| Legacy route | Expired launch context does not govern ordinary stop/destroy; no cleanup clock is borrowed. |
| Current policy | Drift or missing managed policy refuses cleanup without consuming its argv. |

Dependencies: frozen control deadline contract and common `simple_container_control_v2` facade. No compiler builds/checks or executable tests were run for this source slice; lightweight source guards are reported separately.

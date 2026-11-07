# Fresh configured execution-user specification

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_execution_user_v2_spec.spl`.

Manual source mirror: six authored scenarios, UNEXECUTED. No native Podman or effective-UID qualification.

| Scenario | Oracle |
|---|---|
| Exact inspect | Independent full typed format/ID vector; unsafe IDs refuse. |
| Configured user strings | Numeric/name/group and escaped literal strings preserved. |
| Strict bounded JSON | Empty/control/overbound, nested, duplicate, trailing, unknown, wrong type and foreign operation refuse. |
| Common receipt | Actual managed scripted create then fresh exact inspect; selected user, timestamp, pin and canonical codec checked. |
| Pre-query authority | Wrong native ID/op, body digest or scope gives no receipt and executor attempt count remains one from create. |
| Failed observation | Empty/saturated/error/foreign-label output gives no receipt; changed engine baseline does not consume the queued inspect. |

Configured user metadata remains distinct from an observed running-process UID. Dependencies: common execution-user receipt/facade source and the existing bounded captured process owner.

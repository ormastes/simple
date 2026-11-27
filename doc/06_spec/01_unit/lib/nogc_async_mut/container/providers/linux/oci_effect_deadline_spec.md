# Linux managed launch deadline specification

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_effect_deadline_spec.spl`.
Evidence: **AUTHORED_UNRUN**. These eight cases use explicit scripted effects and
clock samples. They do not qualify a native pre-exec clock or a live Podman.

| Case | Observable assertion |
| --- | --- |
| Missing deadline | Managed create rejects and consumes no scripted create. |
| Expiry after earlier verification | An earlier sample has one millisecond remaining; the final sample at expiry rejects without consuming the effect. |
| Policy observation ordering | Changed engine identity rejects before the final clock is sampled. |
| Valid launch | The effect is consumed once; the independently configured 5000 ms lifetime remains unchanged despite one millisecond of admission validity. |
| Failed clock | A negative sample rejects without consuming the effect. |
| Wrong action | A start-only context cannot authorize create. |
| Production clock isolation | A production provider refuses the scripted clock setter. |
| Managed native identity | Names, partial IDs, option-like IDs, multiple IDs, and extra output leave an uncertain prepared intent; no fabricated absence or release. |

The trusted Host must authenticate the grant and approval before constructing
the common deadline. The fixture does not establish grant authenticity. Its
create argv comes from the existing builder for setup; independent argv-vector
specifications remain the builder oracle.

The real captured-process owner must recheck after governor admission and at
native pre-exec. A timeout/output-limit result or uncertain execution error must
retain recovery ownership; neither means that the workload is absent. Native
capture tests, common API integration, live rootless Podman, and the full runtime
matrix remain pending. No check or build was run for these cases.

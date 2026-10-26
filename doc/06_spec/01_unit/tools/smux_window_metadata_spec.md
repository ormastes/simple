# Window metadata rename unit controls

Source: `test/01_unit/tools/smux_window_metadata_spec.spl`.
Status: **NOT_RUN — five authored cases, zero executed**. Manual mirror prepared
from source; canonical docgen and coverage measurement remain pending.

| Case | Observation |
|---|---|
| Canonical name boundaries | Spaces, BMP/astral Unicode and exact 256-byte names survive unchanged; empty, oversized, NUL, C0, DEL and C1 names refuse. |
| Membership | Unknown session/window and foreign-session membership refuse without altering the input value. |
| Ambiguity | Same-session peer names and IDs refuse; another session's display name is allowed. Renaming to the target's own ID does not change its identity. |
| No-op | Identical name yields equal complete service configuration. |
| Preservation | Rename and inverse preserve active state, manual geometry/reference canvas, zoom, presentation, pane identity and child/content incarnation fields. |

These use explicit registry values and no host calls. They do not prove native
cleanup, runtime provider availability, wire dispatch or full CoreMux support.

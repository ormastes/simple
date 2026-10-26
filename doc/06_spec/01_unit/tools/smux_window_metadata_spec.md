# Window metadata rename unit controls

Source: `test/01_unit/tools/smux_window_metadata_spec.spl`.
Status: **NOT_RUN — five authored cases, zero executed**. Manual mirror prepared
from source; canonical docgen and coverage measurement remain pending.

| Case | Observation |
|---|---|
| Canonical name boundaries | Spaces, BMP/astral Unicode and exact 256-byte names survive unchanged; empty, oversized, NUL, C0, DEL and C1 names refuse. |
| Membership | Unknown session/window and foreign-session membership refuse without altering the input value. |
| Nonunique labels and stable identity | Same-session duplicate labels and labels equal to a peer ID are accepted. Exact ID lookup and a subsequent sibling rename still address the correct window; cross-session and own-ID labels do not change identity. |
| No-op | Identical name yields equal complete service configuration. |
| Preservation | Rename and inverse preserve active state, manual geometry/reference canvas, zoom, presentation, pane identity and child/content incarnation fields. |

These use explicit registry values and no host calls. They do not prove native
cleanup, runtime provider availability, wire dispatch or full CoreMux support.

Cycle 2 corrects the original uniqueness policy: window names are labels and
need not be unique. Canonical name validation and exact membership remain;
future name-based ResolveTarget must reject ambiguous matches instead of picking
one. This spec does not implement or qualify that future resolver.

# phase2_mir_glob_import_dict_payload_2026-11-15

With `use std.common.traceability.model.*`, the frozen Phase 2 compiler reports
`enum payload dictionary key annotation mismatch` for every `SdnValue.Dict({...})`
literal. Files using identical literals without that glob compile. Root cause not
isolated; workaround is an explicit import list. Modules: app.traceability.query_render_v1,
query_render_refs_v1, snapshot.worktree_query_v1, lib.common.traceability.query_refs_v1,
query_nodes_v1, annotations_v1. Remove when the pinned compiler is past this.

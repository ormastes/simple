# Native entry closure drops numbered editor declaration owners

Status: source repair and five filesystem regressions prepared; execution
pending the root-owned cached rebuild. No native PASS or admission claimed.

The Phase4 Cranelift CLI has 110 failed terminal modules. Its authoritative
ledger contains no row for `src/lib/editor/00.common/types.spl` or
`keybindings.spl`, although both physical files exist in snapshot
`scv-revision-v1-2fd2b1262aa16691114647a0cded087362e5ed6995a0fae73ccaabb6b8a3df51`.
The missing owners declare EditorBufferId, EditorDocumentId, EditorViewport,
EditorMode, KeyBinding and KeybindingConfig used across the editor failure
family. The source path and HIR diagnostics are retained in
`runtime/windows-restart-20261004/phase4-failure-groups/`.

The split `native_build_closure.spl` probes only exact directory segments,
so `std.editor.common.types` cannot discover `editor/00.common/types.spl`.
The older `native_build.spl` and the driver already implement numbered
directory traversal. The repair delegates the split walker's exact-path miss
to the existing driver owner, avoiding another implementation. Exact-file and
exact-package precedence remains unchanged. The shared driver traversal now
also supports a numbered final package directory and rejects multiple numbered
siblings instead of choosing a filesystem enumeration winner. Directory
traversal requires real directories; a regular Git-link placeholder is not a
directory. No path is manually inserted into an admitted source list.

The fixture exercises a nested editor owner, numbered final mod/init owners,
ambiguity and exact precedence, rejection of a placeholder, and a genuine
in-root link created by the checked native snapshot-link owner. The linked
test fails if link creation is unsupported; it does not skip or substitute a
mock. These are resolver-level tests, not full SCV admission tests.

The patch does not change authenticated closure selection or its authority
bindings. Both touched production files were compared against repaired
integration `147d2028252`; their base bytes matched. A new producer containing
this resolver change and its validated source/policy identities must recompute
the affected closure before its receipt is reusable. No epoch-only reuse or
identity stamp rewrite is allowed. Existing failed caches and receipts remain
untouched. Actual source readback and snapshot membership checks remain in
their canonical owners after path resolution.

TRACE32 is a separate materialization failure: its 47-byte link placeholder
cannot be resolved until the real target is materialized and included in source
authority. This repair does not invent those missing source bytes.

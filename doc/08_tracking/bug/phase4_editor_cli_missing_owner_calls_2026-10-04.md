# Phase4 editor and CLI missing owner calls

The Cranelift full-CLI retry has 2,571 terminal module rows: 2,461 PASS and
110 FAILED. These are module outcomes, not test counts. Its exact failure
diagnostics are retained in
`runtime/windows-restart-20261004/phase4-failure-groups/cranelift-cli-diagnostics.json`.
The symptom assignment gives this lane 36 editor/CLI modules; this patch only
repairs the independently demonstrated missing calls listed below.

* `targets_cli`: import the existing `ResolvePlan` from `target_resolve`.
* CLI main/help: import `get_version` from the same owner as `print_version`.
* Wiki CLI: import existing `load_config` used for backend selection/editor.
* Attachment, workspace-symbol and LSP-edit helpers: invoke the real filesystem
  facades already intended by their imports, replacing unresolved raw names.
  Nullable reads and boolean writes preserve the existing failure decisions.
* Markdown search: import the existing `md_wiki_document` constructor.
* Optional panel/channel lookup: return the language's `nil` sentinel instead
  of the unresolved identifier `none` (three return sites).

Two new attachment regressions read actual published bytes, preserve previous
destinations on duplicate names, reject missing input and admit a real empty
file. Existing target, wiki and editor specs cover the remaining callers.
All native execution remains UNRUN pending the root-owned cached rebuild.

This patch does not claim the shared missing editor type owners are repaired.
They were omitted from the terminal closure and are handled by the separate
numbered-directory resolver repair. TRACE32 is also not fixed here: the actual
Windows checkout materialized `src/app/t32_cli` as a regular 47-byte Git link
placeholder, and the frozen snapshot has no corresponding directory. Its
physical source must be materialized and admitted; adding imports cannot make
missing source bytes valid. No live checkout/cache/receipt was modified.

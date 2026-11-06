# LSP document authority expert

Read `doc/07_guide/tooling/lsp_revision_bound_code_actions.md`. Reuse the existing
LspServer owner, never a second mutable overlay registry. Code-action conversion
is a wire boundary, not an apply engine: preserve the compiler shared source-edit
owner and editor version checks. Before binding a child result to an editor
version, require exact analyzed-source stamps; before/after disk equality alone
is not proof. Malformed or stale workspace edits must disable the entire action
and remove its follow-up command. Never interpret isPreferred as auto-apply
authority. Full unsaved-overlay and partial-application acceptance remain open.

Keep synchronization validity and newest observed version in the same owner.
Malformed newer updates revoke authority without replacing accepted source.
Preserve document/byte/URI caps and reclaim budget on replacement and close.

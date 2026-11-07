# code action revision spec

Status: authored operator outline, not generated execution evidence.
Generation and execution require the admitted pure-Simple runtime.

1. Bind deletion and multiple edits to the exact editor version.
2. Reject mismatched and missing analyzed-source stamps.
3. Bind every target URI independently; reject missing authority.
4. Reject stale producer versions and duplicate document entries.
5. Reject overlapping edits and remove follow-up commands.
6. Reject malformed later edits and split UTF-16 surrogate positions.

See `doc/07_guide/tooling/lsp_revision_bound_code_actions.md` for authority and
remaining acceptance criteria. No public-protocol or release PASS is claimed.

7. Refuse more than 128 actions before edit traversal.
8. Reject simultaneous changes/documentChanges and a raw source path inconsistent
   with the analyzed revision, even when a matching stamp is supplied.
9. Distinguish a valid empty result array from malformed, titleless or null rows
   using the same result-admission helper called by the live handler.

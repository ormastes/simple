# Warning autofix trusted stale and conflicting coordinates

`entry_and_fixes.apply_collected_fixes` ignored Replacement.file, flattened edits, and called the permissive splice helper directly. A replacement for another source could alter the selected file; overlapping/invalid ranges could produce corrupt output. Reading the target after lint did not prove it was still the diagnosed revision. The sibling simple-fix route also lacked source-pinning checks before disk writes.

The source candidate adds one shared edit-admission leaf and wires both real routes. A retained analyzed-source argument is mandatory for lint application; invalid plans and stale files return actionable errors. The known filesystem race window and nontransactional multi-file write semantics are documented in the design.

The existing @allow file attribute also lacked explanation requirements. Missing descriptions now retain the original warning and emit LINTALLOW001. No automatic suppression, unsafe marker, or guessed Any rewrite is provided. Public API regression cases are authored but UNRUN; compiler/CLI execution is not authorized in this campaign.

Revision 2 reconciles existing `fix_atomic_write_failure_check.spl`: its directory target now fails source admission before any atomic write. The retained filename preserves callers, while comments/output accurately describe invalid-source rejection and directory preservation. This oracle does not exercise file_atomic_write failure. Actual atomic-write-failure coverage remains unqualified; no fake provider or permission assumption was introduced. Production implementation and 17 new scenarios are unchanged.

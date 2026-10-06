# Imported CoreLexer instance methods fail in the test generator

Status: workaround candidate, native UNRUN; root cause not yet proven.
Producer29f26fc8b054abc170d198d6a837b9e1d348476379266546c5c89577efa0f07a,
sourceb4a202, generator packet six-products-b4a202-29f-j40-preparation.
Closed compile exit1 reports disable_forced_indentation, pop_indent,
char_at_pos, char_slice and enable_forced_indentation. Duplicate log wrappers
must not be counted as independent errors. Reported18:17 points to _NL rather
than the actual method calls301/313/750/757/764; no method-owner trace available.

All receiver locals are already explicitly CoreLexer. b4 includes73b989 owner
precedence, so repeating that fix does not establish repair. Current3f0 lexer,
owner module, symbol table and imported surface materializer match b4 bytes.
3f0 MIR differs and lacks73b989; preserve that separate repair when composing.

The narrow workaround routes these five calls through free functions in the
CoreLexer declaration module, following core_lexer_next_token. Read operations
keep the original codepoint implementation. Mutators return the updated value
for the existing single writeback. No MIR owner validation is relaxed and no
global storage ownership is modified. Registration remains pending through the
canonical bug/workaround API; this document is not a registered receipt.

Focused fixtures: imported-inline main has6 real checks and exact PASS label;
negative_owner must reject NoMethods.pop_indent without borrowing the sibling
method (crash/unrelated import error is not a pass). owner_wrappers has12 checks
covering Unicode/codepoint boundaries, value-copy alias preservation, and repeated indentation updates/no-op boundaries.
All native/parser checks UNRUN. The imported-inline fixture is a candidate
reproduction, not proof it recreates the large generator closure failure.

After pinned source publication, run focused fixtures on each backend. If they
qualify, rerun the actual generator and inspect exact failure changes. Revert
the tagged wrapper calls only after a structural owner-transport fix is applied
and both focused plus real-generator qualification pass. No time/RSS improvement
claim yet; wrapper value copies follow existing behavior but require measurement.

## Followup on source606 / producer7404

Actual helper generator failure again reports four imported CoreLexer methods
and byte_at receiver-not-text; captured locations identify stale declaration
spans, not reliable call sites. Exact a3e wrapper source/fixtures are reused;
606's two original lexer files match the a3e base bytes. Existing typed-receiver
workaround db697 is already present and must not be claimed as a new repair.

Prior79cb/producer29f evidence: imported-inline6checks passed both backends;
wrong-owner compile rejection was observed; real CoreLexer wrappers failed in
unrelated ProcessObservation enum lowering, so the wrappers remain unqualified.
Do not count duplicate diagnostic marker records as independent failing cases.

The byte_at compiler guard candidate now considers the already established
receiver_declared_type Str proof before lowered-local metadata, matching the
other primitive text builtins. It does not accept Any or a nominal receiver
without a resolved custom method. Seven-check UTF8/imported-field/custom-owner
fixture plus a nominal negative fixture pin this boundary. These new fixtures
and producer7404 actual helper rerun are UNRUN; declaration-proof recovery is
not yet established as the cause of the large-closure failure. Existing
receiver guards and owner validation remain enabled. A compiler rebuilt with
the guard candidate is required before claiming a byte_at producer repair.

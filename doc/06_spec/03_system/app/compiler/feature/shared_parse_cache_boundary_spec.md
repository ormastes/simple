# Shared parse cache boundary

Evidence class: **host-fixture**. Execution: **UNRUN**. This manual was authored
from the executable SSpec; qualified SPipe docgen and its zero-stub receipt are
still required. It must not be represented as generated or passing evidence.

Executable: `test/03_system/app/compiler/feature/shared_parse_cache_boundary_spec.spl`.

1. Preprocess a portable function for Windows and Linux. Check identical
   parser input/cfg identity, then check that a Windows-only declaration differs.
2. Change each semantic key field independently. Require a different key;
   missing authority fields must produce no key.
3. Parse a real function returning 73 and encode its actual flat pools. Decode
   the immutable cell, restore the module and inspect the function's AST body.
4. Parse an unrelated function between capture and restoration. Check that
   restoration contains only the portable function, with its original literal.
5. Give the decoder a valid envelope containing malformed flat pools. Envelope
   admission may succeed; module hydration must fail. A subsequent real parse
   must return the expected module, proving parser state was not poisoned.
6. Corrupt and truncate real cells, substitute an address and change codec or
   envelope version. Require rejection while the unchanged cell remains valid.
7. Resolve distinct frozen host source roots to one portable logical path.
   Reject traversal, ambiguous source anchors and private artifact/session names.

These twelve scenarios call production owners with concrete assertions. They
do not prove cross-host publication, filesystem no-follow behavior, concurrent
writers, private HIR/native generation rejection, or deployed host behavior.
Those required checks are tracked in
`doc/03_plan/sys_test/shared_parse_cache_crosshost_acceptance.md`.

The compiled native probe additionally requires parser-call delta zero on
consume and one on publish/reparse, a valid target receipt, and AST literal 73.
Trace lines and a directory mount alone never count as semantic hydration.

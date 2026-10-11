# Retained authoritative parse reuse

Executable: [build_cache_parse_reuse_spec.spl](../../../../test/00_formal_verification/compiler/build_cache_parse_reuse_spec.spl).

Status: authored, unexecuted. This manual has not been admitted by SPipe docgen.
Requires the exact released/candidate frontend closure and an isolated admitted
cache; the stale shared frontend is a different source cut.

1. Parse `held()` and retain the serialized flat frame and rich AST. Read the
   actual `flat_parse_module_body_calls` counter: exactly one parse occurred.
2. Parse another module, which resets the global pools. Check the original
   function's retained literal and the new function's literal independently.
3. Restore the retained frame. The returned literal is unchanged and the parser
   counter does not increase. Reject a frame with trailing corruption, then
   recover with one authoritative parse.
4. Give the full frontend captured source A while the file path holds source B.
   Parse A and B once each, then reuse A without a third parse. This pins the
   already-released supplied-source key fix.
5. Supply changed invalid syntax. Require actual parser errors and no successful
   cache publication; the parse count increases once.

This proves neither TLDR/HIR producer wiring nor shared build/test runner cache
ownership until their actual entrypoints use the same retained parse owner.
Borrowed transient-scope promotion and OS concurrent lock recovery need their
separate runtime checks. Decoder success alone is insufficient.

Evidence/report: [formal verification report](../../../09_report/build_cache_formal_verification_2026-10-10.md).

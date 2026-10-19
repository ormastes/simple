# Typed managed parser diagnostic SDN

Executable: `test/03_system/compiler/incremental/managed_parse_diagnostic_v2_spec.spl`.
REQ-IM-008/012/016; NFR-IM-004/005/008. Status: authored, runtime/docgen UNRUN.

1. Encode and strictly decode actual DiagnosticV1 Warning and Error records,
   preserving located Unicode text, escaping and source-bound identity notes.
2. Change source digest, logical path, severity or warning message independently;
   require rejection, not a successful forged diagnostic.
3. Add trailing data/whitespace, alter record version, or submit JSON; require
   rejection by strict parsing or canonical equality.
4. Supply unsupported spans, nested diagnostics, severity or duplicate identity
   notes; require explicit rejection rather than dropping information.
5. Exercise exact and over-limit message bytes, multibyte UTF-8, oversized input,
   nesting and node bounds. No truncation or recovery parse is accepted.

These tests cover the foundational codec, not V2 module/action aggregation,
warning-success artifact transport, parent replay or live worker qualification.
The existing worker warning-mode refusal remains active.

# Static conditions, symbolic TLDR, and build pruning requirements

Status: selected design requirements; implementation and native performance unverified. Date: 2026-10-06.

Authority: [user proposal](../../01_research/local/simple_static_when_tldr_build_pruning_plan.md), preserved verbatim, SHA256 `03c2004edc362510f91b0a9b6458985d83763d978119d6b33a926c8d9ffb9220`. These requirements are already selected. The local knowledge receipt is `.spipe/static_when_tldr_build_pruning/knowledge_selection.sdn`; it does not admit remote knowledge, implementation, or release.

| ID | Required behavior | Acceptance family |
|---|---|---|
| REQ-001 | One typed Boolable condition model for if/while/guards/@when. Arbitrary enum values have no implicit truthiness. Static @when adds an early-evaluation phase restriction. | T01 |
| REQ-002 | Builtin one-of and set domains, stable provider/member identities, sealed complete extensions, fail-closed unknown/wrong/ambiguous/dynamic members. | T02 |
| REQ-003 | Dependency-time conditions admit literals, typed predicates, not/and/or/grouping and explicitly registered dependency-safe conversions; no arbitrary CTFE, I/O, imports, host probing, or runtime state. | T03 |
| REQ-004 | One bounded structural scan preserves exact nested when/elif/else guards, source spans, and lexical validity in inactive regions. False interiors need no AST/type/import resolution. | T04 |
| REQ-005 | Interned guard algebra has conjunction fast path, bounded DAG fallback, local simplifications and deterministic serialization/rendering independent of discovery order. | T05 |
| REQ-006 | Versioned portable symbolic TLDR/AST preserves declarations, guarded references and deferred-region coverage; selected target does not erase reusable symbolic facts. | T06 |
| REQ-007 | TLDR imports derive from reachable public semantic references, including required generic/inline/const/macro/advice bodies. Within TLDR/public-summary projection, unused private imports are neither resolved nor copied. Required invalid references fail. | T07 |
| REQ-008 | False guard evaluation precedes candidate expansion, filesystem probes, source reads and build submission for dependency modules. | T08 |
| REQ-009 | Symbol/effect closure preserves initializers, reexports, traits/coherence, extensions, macros/CTFE, aspects, registrations, FFI/link metadata, reflection and test roots. Unknown coverage never authorizes pruning. | T09 |
| REQ-010 | Source/TLDR/portable AST/OBJ/SMF identities bind their exact semantic inputs; domain seal, condition policy, dependency, aspect cut/capture and runtime format changes invalidate affected results transitively. | T10 |
| REQ-011 | Compiler owns one planning/cache path for standalone and runner clients. Only exact active missing work is enqueued; TLDR readiness may unblock compilation, object readiness gates linking. | T11 |
| REQ-012 | GPU/SIMD acceleration is optional transport for identical facts; checked scalar fallback handles absence/unsupported inputs, never false or incomplete summaries. | T12 |
| REQ-013 | Compatibility aliases normalize to typed atoms; versioned lint/warning/reliability policy migrates cfg/string conditions and enum truthiness without silent bootstrap behavior changes. | T13 |
| REQ-014 | Counter and native profiling evidence covers cold/warm/incremental/contention, broad/pruned output parity, work avoided, standalone/runner parity and resource bounds. | T14 |
| REQ-015 | Source observation may avoid hashing only under independently validated immutable snapshot/watcher authority. Mtime alone is insufficient; equal-content edits reuse semantic results. | T15 |

The final feature includes every requirement. A bounded first slice is an internal sequencing decision, not a reduction of scope. No-condition files still require ordinary language parsing; this feature avoids extra guard work. Side-effect-import syntax is not added in this change: existing observable effects remain conservatively rooted. Normal executable diagnostics for invalid unused imports remain the existing language policy; public-summary-only projection must not require them.

See [architecture](../../04_architecture/static_when_tldr_build_pruning.md), [detail](../../05_design/static_when_tldr_build_pruning.md), and [test matrix](../../03_plan/sys_test/static_when_tldr_build_pruning.md).
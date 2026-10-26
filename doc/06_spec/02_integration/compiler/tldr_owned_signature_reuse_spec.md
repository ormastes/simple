# Compile-owned TLDR signature reuse

Source: `test/02_integration/compiler/tldr_owned_signature_reuse_spec.spl`.
Status: six authored criteria, all UNRUN. This manual is source-authored, not generated execution evidence.

| Requirement | Setup and action | Required assertion | Evidence |
|---|---|---|---|
| REQ-OWNED-001 | Project a typed archive through the actual archive admission function. | Retained names, linkage, parameter names/types and return type equal direct admission. | UNRUN |
| REQ-OWNED-002 | Resolve the same admitted function twice under one alias and once under another. | No errors; repeated alias preserves symbol ID; linkage and nested signature arrays remain unchanged. | UNRUN |
| REQ-OWNED-003 | Construct a legacy two-field carrier, then attempt a tampered legacy carrier and the raw registration API. | Legacy valid header registers; both raw tamper paths reject without publishing a symbol. | UNRUN |
| REQ-OWNED-004 | Admit a fresh carrier under changed source and variant digests. | New bindings and payload digest differ; old payload fails against current authority; old carrier remains unchanged. | UNRUN |
| REQ-OWNED-005 | Supply an unsupported parameter type through actual archive projection. | Admission fails before a typed carrier is returned. | UNRUN |
| REQ-OWNED-006 | Read one admitted immutable carrier from two lowering instances. | Registration remains local to each symbol table and retained parameter names remain unchanged. | UNRUN |

The fixture constructs decoded archive/receipt/index values to test this bridge. It does not qualify the upstream disk pinning or source snapshot protocol. Changed variant coverage is a binding test, not evidence that all aspect/capture inputs enter the existing variant digest.

No compiler, interpreter, benchmark or diagnostic was launched for this successor. Prior eight membership tests and twelve rejected-codec tests do not qualify these six new criteria. The shared feature's three diagnostic cycles are exhausted. Native correctness, parse work-count measurement, equal-or-faster timing, RSS, transient-scope lifetime stress, full core/MCP smokes and release verification remain UNRUN.

Source review establishes that the non-nil consumer branch does not call `tldr_function_header_admit_v1`; only the legacy nil branch does. This is not a measured performance result. The source fix does not implement cross-process build-runner sharing or establish the requested 0.1-second compile target.

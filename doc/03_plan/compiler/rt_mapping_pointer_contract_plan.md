# rt_ Mapping and Pointer Contract Plan

Design: doc/05_design/compiler/rt_mapping_pointer_contract_design.md

| Stage | Scope | Status |
|---|---|---|
| R0 | Baselines and negative fixtures | Partial: pointer-return guard, #5648 |
| R1 | Canonical contract records and profile view | Not started |
| R2 | Compiler-generated mapping and pointer evidence, both directions | Not started |
| R3 | End-of-build all-variant audit | Not started |
| R4 | Warn-to-error migration | Started: shrink the 38-row return baseline |
| R5 | Retire overlapping scanners and lists | Not started |

Current gate: scripts/check/check-rt-pointer-ref-map.py. At #5648: 270 edges, 38 baselined, 138 UNKNOWN.
Text scan only. Compile and link are UNTESTED on every host; parameters are not yet checked.

Migration blocker: the interpreter keeps `T?` wrapped in typed bindings, fields, `.push` and `for`.
Each signature change must update its call sites and carry a RED-to-GREEN spec.

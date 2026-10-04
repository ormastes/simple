# Mach-O TextAPI v4/v5 acceptance

Nine authored scenarios in `test/03_system/app/compiler/feature/item4_macho_tbd_spec.spl`.
**Simple execution UNRUN**. This manually authored companion is not a generated
test receipt. External fixture evidence is recorded separately below.

| Requirement | Scenario |
|---|---|
| ITEM4-REQ-006 | Positional and named leaf stubs, both formats and both CPUs, produce independently checked real executable-image bytes. |
| ITEM4-REQ-006 | Selected targets preserve packed versions, install identity, and format-specific deployment semantics; lowering leaves SDK absent. |
| ITEM4-REQ-006 | Rich target-scoped ObjC, weak, TLV, client, umbrella, inline-library and reexport metadata survives reading; unresolved closure/policy refuses leaf lowering. |
| ITEM4-REQ-006 | Duplicate keys, truncation, target mismatch and byte/token/depth/library/symbol/name budgets reject. These are logical parser budgets, not memory enforcement. |
| ITEM4-REQ-006 | An unmatched inline library has no fabricated selected identity; its scoped install-name declarations remain available. |
| ITEM4-REQ-006 | ObjC names expand to ABI symbols, weak/TLV flags survive, and real x64/ARM64 TLV relocations link through typed providers derived from each format. |
| ITEM4-REQ-007 | Malformed selected stubs preserve destination sentinels without archive fallback; removing only the stub permits the unchanged plan to link the real archive. |
| ITEM4-REQ-006 | Malformed unselected groups, overlapping install identities, incompatible unselected versions, duplicate unselected umbrellas, escaped duplicate JSON keys, wrong format versions and version component overflow reject before selection. Arm64e and Catalyst cannot satisfy baseline arm64 macOS. |
| ITEM4-REQ-006 | `$ld$` directives remain literal reader metadata and reject at unsupported lowering rather than becoming ordinary exports. |

Fixtures are authored or converted from repository-authored binaries using LLVM
21.1.8 `llvm-readtapi`; `test/fixtures/linker/macho/RECIPE.md` records commands.
Both leaf and rich v4/v5 comparisons succeeded externally. LLVM21 accepts
identical duplicate JSON keys, so the required JSON duplicate rejection is an
intentional stricter policy, not an LLVM agreement claim. V4 deployment is None;
V5 omitted deployment means Some(0), while explicit arm64 deployment remains11.
No SDK version or VM address is inferred from absence.

After independent runtime admission:
`<runtime> test test/03_system/app/compiler/feature/item4_macho_tbd_spec.spl`

Open full-SDK obligations include transitive reexport closure, client/umbrella
access binding, selected weak import coalescing, actual SDK/framework workloads,
Darwin dyld execution, bounded whole-job enforcement and host qualification.
Reader metadata coverage does not claim these behaviors are implemented.

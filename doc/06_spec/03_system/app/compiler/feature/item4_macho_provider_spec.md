# Typed Mach-O provider boundary

Eight authored ITEM4-REQ-006 scenarios in
`test/03_system/app/compiler/feature/item4_macho_provider_spec.spl`.
**UNRUN**, manually authored companion; no generated execution evidence.

| Scenario | Actual contract |
|---|---|
| Binary/typed equivalence | Real x64 and ARM64 dylibs validate then project into metadata. Typed and legacy image paths agree; independent CPU, entry, version, bind, pointer and branch checks prevent equivalence alone being the oracle. |
| Optional deployment | Absent min/SDK stay absent and link without invented VM metadata; a shape-valid non-macOS platform and a declared newer minimum reject at the hosted consumer. |
| Binary validation | A genuine symbol-table fallback works before an export address is corrupted; projection still rejects the unmapped symbol. Binary SDK zero stays Some(0). |
| Shape rejection | Wrong CPU/platform, invalid names/versions, duplicate exports, invalid kind, out-of-range reexport ordinal and malformed restrictions reject. |
| Selected unsupported semantics | Selected weak, absolute and reexport imports reject rather than being normalized to ordinary exports. Valid access restrictions retain their values and reject at the unbound hosted policy gate. |
| Real TLV provider | Both architectures preserve actual TLV export kind and emitted instruction/pointer behavior through typed linking. |
| Binary access commands | Size-preserving LC_UUID replacement creates actual LC_SUB_CLIENT/LC_SUB_FRAMEWORK command bytes; projection retains policy and hosted linking refuses unsupported access binding. Command-relative offset at the end, missing terminator and empty name each reject. |
| Unused metadata | Valid unused weak/reexport/resolver metadata remains admissible; no blanket rejection substitutes for selected-import semantics. |

All binary inputs derive from the authored fixture corpus and its LLVM recipe.
The access-command mutation preserves every payload offset and command size.
The provider type has no virtual-address fields; binary validation precedes its
projection. No fake dylib is synthesized from typed metadata.

After independent runtime admission:
`<runtime> test test/03_system/app/compiler/feature/item4_macho_provider_spec.spl --native-backend=llvm --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts --verbose`

Still open: v4 YAML and v5 JSON TextAPI parsing, SDK target filtering, transitive
reexport closure, client/umbrella permission binding, supported weak import
coalescing, actual Darwin loading, full SDK application execution and resource
qualification. This is a typed integration prerequisite, not completed SDK support.

Pending execution follows [the item4 native execution gate](item4_linker_execution_gate.md).
This command is an unexecuted recipe, not proof that the current CLI or generated
entry is admitted. Account for all 8 declared scenarios and their actual
assertion behavior; zero reported examples or missing scenario results cannot pass.

# Abstract/external text system test plan

Status: authored tests, **UNRUN** on this current base. No compilation, check, test or bootstrap is authorized by this source-port task. Existing failed/exhausted qualification campaigns remain unchanged.

| Executable | Real acceptance oracles |
|---|---|
| `test/03_system/lib/encoding/abstract_external_text_spec.spl` | REQ-001–007: generic primitive/external contracts, exact typed Result payloads/errors, metadata retention, UTF16LE/BE and UTF8 roundtrips, NUL, scalar cardinality, strict malformed offsets, defensive copies, split BOM/scalars, independent state, sticky errors, terminal lifecycle |
| `test/01_unit/lib/encoding/bom_admission_spec.spl` | BOM-only admission, forbidden offset, required prefix with invalid payload, metadata rejection |
| `test/01_unit/lib/common/encoding/unicode_scalar_codec_spec.spl` | Exact UTF8 width/range endpoints including 8/128, surrogate gap, supplementary scalar/max, invalid byte values, overlong/truncated/multiple scalars and out-of-range integer rejection |
| `test/fixtures/native_abstract_external_text/main.spl` | Existing native generic dispatch, strict conversions, packed-provider basis probe, carry and truncation fixture; no new harness |

The system spec imports the public module from a separate module and reads all ExternalChar accessors and decoder.pending_byte_count. Private constructor/field enforcement still needs a separate negative compiler qualification; this port does not claim one. The actual primitive char cast/return ABI and packed provider identity must be admitted separately from hosted C behavior.

Future root-authorized verification needs an exact source-bound self-hosted runner with proven test/check capability, actual provider linkage and retained source/tool manifests. The captured native-build-only compiler is not test/check authority. The pure-packed runtime's three failed attempts and prior physical-storage attempt caps are not reset by these specs. No fourth retry is prescribed.

No duplicate run after a criterion passes. Remaining gates include admitted spec execution, scalar/trait dispatch, privacy, memory/OOM/refcounts, branch coverage, generated manual quality, core/MCP/LSP smoke and realistic memory/performance measurements. File/network/environment/argv/process/console/path adapters belong to the selected plan's future integration work. Source status and execution status must remain separate.

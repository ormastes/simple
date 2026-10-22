# SMF template extraction must use recorded section types

Source-confirmed mismatch: canonical driver.smf_writer emits Code at index0
and TemplateCode at index1 when templates exist without Data. The existing
SmfReaderImpl.find_section_by_type assumed TemplateCode index2. The public
DeferredMonomorphizer file API had no extraction and was recently repaired to
refuse rather than falsely succeed. This packet implements the actual path.

Canonical ownership: SmfReaderMemory now owns typed lookup and typed reads.
find_section_by_type scans recorded type bytes, returns Ok(-1) when absent,
and rejects duplicate requested section types. read_section_by_type propagates
precise errors, supports uncompressed outer1.0/1.1, and rejects unknown/raw
nonzero compression rather than trusting CompressionType.from_u8's fallback.
The old file shim's i32 lookup delegates, keeping -1 for missing/errors.
Its symbol-specific template reader delegates to typed section extraction;
its existing symbol-relative record interpretation is otherwise unchanged.

The public file wrapper uses existing file_read_bytes_result, canonical
SmfReaderMemory.from_data, typed TemplateCode extraction, then the reviewed
GTPLv2 transaction. It reads real files and populates actual FunctionDef/other
template records. The template section wire value12 is named at the canonical
reader because the existing general SectionType enum lacks that variant; it
matches the existing canonical driver writer, not a new format.

Bounds: canonical header conversion checks raw offset plus stub/data base by
remaining-length comparison before addition. Section-table offset/count are
checked before string-table discovery or entry reads. Shared section bounds
check payload offset/size before addition or copying. Explicit string tables
use that same helper; implicit string-table location validates symbol offset
and count before multiplication. Existing read_section_by_index reuses bounds
while preserving its [] failure API. No second header/section parser exists.

This changes a legacy helper's fixed-index behavior deliberately: callers now
observe actual wire types. derive_section_type_from_index remains an explicit
legacy mapping utility; it is not used for typed section admission. Unknown
unrequested section types are skipped, while missing/duplicate requested types
refuse. Existing GTPLv2 version checks, complete-record transaction and
last-definition-wins policy remain unchanged; failed file/section/GTPL paths
do not mutate old template cache rows. No guessed index fallback is retained.

Complexity is O(section_count + payload_bytes) per extraction, with existing
whole-file input retention plus one section-byte vector and incoming template
delta. Symbols are not parsed for the deferred file path. The file shim retains
its existing eager symbol behavior. No new hot-loop cache or global retention.
This source bound does not qualify actual allocation/copy cost or performance.

Seven actual API SSpec cases reconcile the prior unavailable-wrapper tests.
They use real canonical writer bytes and checked unique files, test index1 and
reordered sections, preserve old rows on malformed files, cover table/payload
overflow and truncation, explicit string-table bounds, compression/version
refusal, missing-file/header diagnostics, recovery and zero-template controls.
The legacy version control mutates only the canonical header minor byte; it
does not claim every historical layout/profile is qualified. All UNRUN.

No executable generic compilation, mapping, ABI check, specialization gate,
canonical-HIR gate, runtime guard bypass, bootstrap, test-runner or Lean proof
is added. Full generic dynamic execution remains OPEN. This is a source-reviewed
file-to-AST-template slice pending actual compiled/runtime qualification.

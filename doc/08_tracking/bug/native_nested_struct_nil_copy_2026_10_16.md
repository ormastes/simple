# Native nested-record nil copy: MirBuilder manifest payload

Date: 2026-10-16
Bug: BUG-NATIVE-NESTED-STRUCT-NIL-COPY-20261016
Database registration: pending; no admitted database tool available.
Status: source workaround proposed; native qualification UNRUN.
Recover: 6ba18bacb6c431956ade4156b10397250d8e550a

The first TCO control execution of strict candidate 5735AC33C7D49EFEDFBCD6DE1E2F6BC0D638716D89AAE7A6BB063B1643307296 failed with 0xC0000005. The retained Windows dump and mapped COFF place the read of address 3 inside the by-value MirFunction copy at entry to TailCallOptimization.run_on_function, before its source body. Actual captured stack slots contain has_driver_manifest_attr=0 and driver_manifest_attr=3. Heap-record pages were unavailable; no heap inspection is claimed.

MirBuilder.begin_function and its inactive end_function fallback supplied nil to the nonoptional DriverManifestAttr payload while leaving its presence flag false. The baked 0CD6 producer copy guard compares the nested pointer against raw zero, then dereferences the tagged nil carrier 3. The source recursive-copy helper intends to preserve absent nested fields but does not consult the sibling presence flag. A proper producer nil-carrier guard repair remains separate and unqualified.

The bounded workaround supplies the canonical DriverManifestAttr constructor already used by MIR module lowering at both builder sites: Driver kind, zero class/vendor, empty device IDs/version/ABI. Both presence flags remain false. This preserves absence and gives the baked recursive copy a genuine owned payload; no invented layout, fixture payload override, or TCO algorithm change is used. Each site carries the full recover hash.

The inactive end_function fallback also now uses canonical Span.empty() for its required Span field. This is an independent concrete API correction, not the demonstrated cycle2 fault. Legitimately optional current_span, instruction spans and other optional payloads remain unchanged.

The shared actual-builder/TCO fixture now checks that its builder-derived function and the transformed by-value result both retain false manifest presence. Existing local-identity, permutation, return, and operand controls remain intact. These controls have not executed against this source. The final feature qualification cycle3 requires reviewed frozen source, the same persistent entry cache with normal invalidation, strict no-FORCE link review, and a separately authorized single execution. Cycles1 and2 failures and all receipts remain preserved.

Evidence: external mir-tco-local-identity-native-cycle2/windows-fault-evidence/{exception-and-map.json,copied-field-stack-proof.json,nested-absent-manifest-copy-diagnosis-20261016.md}; source-workaround contains original files and proposed diff. Database registration and broad compiler/library/tool gates remain pending.
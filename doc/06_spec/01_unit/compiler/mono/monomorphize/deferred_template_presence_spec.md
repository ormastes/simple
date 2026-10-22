# GTPL explicit AST presence fields

REQ-GENERIC-SMF-TYPED-EXTRACTION. Two actual API scenarios, UNRUN.

1. Serialize and transactionally decode actual FunctionDef/StructDef/ClassDef/EnumDef with absent, present-empty and present-named fields, in both modes. Assert exact presence flags/payloads, function body, unchanged GTPL version2 and zero specialization publication.
2. Serialize stale text under false flags and compare complete bytes against canonical absence. Present-empty adds exactly five four-byte lengths. Decode stale-payload input and assert flags false/payload empty.

The existing transaction suite additionally corrupts a later record's optional tag using actual canonical field readers, and requires precise diagnostic plus unchanged prior cache rows.
No native/compiler run or automatic campaign reset occurred.

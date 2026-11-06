# Compiler lane integration (source only)

Base: b065ff00f44e1d642057673cd1f37e6eaa1b3224. Root is aggregate owner. No compiler, SSpec, native fixture, qualification or planner execution. No push or PR mutation. New optional annotation None patch excluded.

## Original commit mapping

- #7256: `40725185283bd5433c12a8868d2ae391be9a5b58` → `9c98916af6de2eb083290d50e8408ca3ab241bc4`
- #7257: `3a943bdc7c35b5015dd1d5a43510f046ae610812` → `ef935ceee2275377c64f5a8647f734b09acb6283`
- #7257: `db237806739c08b5e0b486c72f13c85efa8b3512` → `98925b60f1d3ac59bbca7b0496c2b42821f84450`
- #7257: `d2b24d4a56cf3557a0607452f0741000519f2b0c` → `3d0bdc948e945528860da6da9f59eda78ede31ce`
- #7272: `45f79fdeed4cd0996979baa44a67af3eb23bf775` → `05840d022b806a1ba140abdbf2f43ce98fe804ef`
- #7276: `ed4220292bfdf2447b94c13f8685a262c1204fe3` → `74ddc20eca3a4b14128aca72b2de63451985509d`
- #7292: `277911aa0e54ec67969e452f6b253df375eed15c` → `81a3d24cee96cc803ee357c14703fb2bc3195e02`
- #7292: `65c2ef8ec445cfd07a9e2cd7cef33051907ef648` → `51457c0a8613b418f5771a91d0e1dc38894aa20d`
- #7292: `dd5605e0faccabfb30ef95c45c71d5272cdb4167` → `79483a0a80da4a62d71731d7bb739634ea04f3fa`
- #7294: `598a264d09735089016f8fc992bbb29337ed6b32` → `7eff369ec865d8f75ed6f4fa002d93469bb2cd7a`
- #7294: `15e87aec6cd9421a467575bff897a0a6adb9348a` → `1b9350d01ef11a400598d2def58a36a7fe67467a`
- #7294: `ed5802e118ff9dc52d005eacc42e23f7032d5ec0` → `96f7c3a061e8fdae023f747b660c14fa98044b52`
- #7294: `1919534c35f063e625acde875b4a27bb953a70d0` → `3052f969e67d9b61a868ca385fa2d6707a250b36`
- #7299: `cf18c45668ed150bdba1de7c4707b5c1ae511f1a` → `bbdeda75f6fa6cac8ceb9688b7fe3ab30b5b46a4`
- #7300: `96c31e0c6041d9cbd32d9d774dacb851a0381de4` → `eae5f3f4647cccd009ffe98ee39cb430fc1c82b1`
- #7306: `40ca5a666c0e9b3c455b5b59d437eb613a82f29f` → `b91d6ad139dacd68a6c67c5fd850544aa7617f61`
- #7310: `85f5cbe8f60f2fea053b1c7ab480cc1fa829b112` → `c2128783ee0e170152bb65d903ae94e93341c531`
- #7316: `272348b96515b400eb1cca268398c1bd39f565f9` → `a484f4f8c27712207d0745e2fa272579e771a60f`
- #7317: `97338ead67de305d69a541bd75dc808c54bf11f2` → `fd4b40c609abd0cb04e9d425f64541f8688e90c7`
- #7309: `60da40e34148dcfb687c0ad1967442bc5c792504` → `ac44f025e16598502631c9b553cf8c95fd445033`

## Conflict decisions and preserved behavior

- #7256: release already implements uniform-I64 zero/subtraction plus signed narrow reduce/sign-extend, alongside independent float-sign bit handling. Kept the production adapter unchanged, removed the incoming unused helper import. Retained helper and native source fixtures/docs; helper-only results cannot qualify production.
- #7299: release already classifies physical F32/F64 before provenance and additionally refuses float operands in runtime normalization. Kept release source byte-for-byte at this step; retained unique tests and evidence.
- #7306: applied actual commit only. Added merge incoming-edge tracking and post-child optional-tail/Let guards. Preserved release current_block_is_dead epilogue, fresh Str HIR reconstruction, generic Result provenance, and exists_scalar_word_locals-based float if-val handling.
- #7316/#7317/#7309 append conflicts in shared fatal-diagnostic bug report retain each complete section. Compiler edits do not conflict semantically.
- #7292 precedes stacked #7294. Selected original PR-only commits, not historical branch ancestry. Each listed original SHA applied once.
- Call declaration remains three fields in src/compiler/50.mir/mir_instruction_kinds.spl:103; #7310/#7316 three-field patterns retained. No separate call-origin ABI migration introduced.

## Verification boundaries

All prior UNEXECUTED/pending gates remain pending; source integration is not runtime PASS. In particular #7294 fixed attempt6 compiled but SIGSEGVed (exit139) before assertions, six-attempt planner budget exhausted; never reinterpret baseline predicates or compilation as fixed-runtime success. The qualification budget remains seven exhausted. Normal hooks were enabled; no bypass used. No new internal None caller patch included.

The historical imported notes preserve their original dates/status; this integration note supersedes any implication that source-only integration itself supplies missing execution or Phase3 qualification.

<!-- codex-design -->
# SCI CLI extension authority v2 detail design

`decode_composition_image_v2` owns section-10/11 paired admission and returns
`SimpleCompositionImageV2`; it does not add required fields to the exported
`SimpleCompositionImageV1`. V2 owns opaque reference handles for the admitted
section bytes/parsed header and decoded authority table. It rejects a
section-10 image without the matching authority view. `main.spl` calls
`simple_core_execute_v2`; it does not assemble an ambient extension table.

`simple_core_route_v2` returns the existing activation evidence plus the
authority namespace locator. `simple_core_execute_v2` resolves that locator
once, applies the lifecycle up to `--`, and either returns local help/completion
or uses the existing SHA-locked provider admit/query/pin/validate/run/release/
close path. Help/complete return before admission. All failure paths carry
typed `SCI_*` or `CLI_EXTENSION_*` codes.

Acceptance scenarios:

1. Legacy image/no section 10 preserves current command CLI behavior.
2. Section-10 extension image without section 11 fails before provider load.
3. Digest-mismatched or route-binding-mismatched authority fails closed.
4. Two same-namespace extension tokens reuse the admitted section-10 handle and one decoded
   authority record; an unrelated corrupt route record is not touched.
5. Extension `--help` and `--complete` are local lifecycle output; `--` makes
   later spellings data; RUN forwards full argv and performs provider validation.
6. A same-provider second namespace, an unsorted section-10 index, a reserved
   byte mutation, or `--complete --` is rejected before provider admission.

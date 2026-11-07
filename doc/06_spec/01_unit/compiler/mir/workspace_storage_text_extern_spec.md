# Workspace storage tagged text ABI

Source: `test/01_unit/compiler/mir/workspace_storage_text_extern_spec.spl`.
Status: three authored scenarios, **NOT_RUN**, manually reviewed mirror; no docgen.

1. **Use the real MIR registry to retain complete native storage text values.**
   Both admission and recovery register text operands 0, 1, 2, 3, 4 and 7 as
   complete tagged values. Quota and hard-byte integer operands remain unchanged;
   neither pointer/length expansion nor reboxing is selected.
2. **Keep nontext native ownership operands outside the text bridge.** Foreign
   homonyms and the token-only observation call receive no tagged-text indices.
3. **Keep native user-observation scope and close-binding bytes intact.** Native
   open preserves cgroup/binding arguments 1 and 2; refresh and close preserve
   binding argument 1. These registry assertions do not replace compiled calls.

The independent execution fixture is
`test/fixtures/native_workspace_storage_text_abi_v1/main.spl`. It directly calls
both real native externs with an embedded NUL and requires EINVAL (-22), bypassing
the public request validator. It remains **NOT_RUN** until an admitted native
Simple producer includes the registry repair. Registry assertions alone do not
prove generated call ABI; the earlier C73-check negative run bypasses MIR lowering.

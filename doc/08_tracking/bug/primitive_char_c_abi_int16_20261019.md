# Primitive Char silently mapped to signed int16_t

Status: source defensive fix authored; all tests/fixtures UNRUN. Physical UTF8 Char remains OPEN.

At release e09fb99f62cf69987d2b7ced7e3cabb643987531 the shared C ABI mapper returned int16_t for MirTypeKind.Char, reached by C backend and both header emitters. Valid supplementary scalars U+1F600/U+10FFFF cannot fit this width; UTF8 inline32 carriers also cannot fit. MIR size metadata additionally reports2 while the verification label says unicode-scalar:u32, so changing this spelling to uint32_t alone would falsely invent compatibility.

The direct Char arm now fails explicitly with E-CHAR-FOREIGN-ABI and requires an explicit scalar integer or versioned UTF8 byte carrier adapter. Other mapping arms remain unchanged. Nested erased pointer/callback/nominal paths still require a separate recursive gate; this patch is not full FFI admission. Existing primitive layout, runtime, JIT and cache identities are unchanged.

Regression: existing c_abi_type_mapping_spec plus direct/C/C++ actual API refusal fixtures under test/fixtures/compiler/char_c_abi_refusal. Expected refusal requires the exact diagnostic; parse/import/arbitrary nonzero failures are not evidence. See doc/05_design/compiler/char_utf8_storage_compatibility_20261019.md for the required full storage migration.

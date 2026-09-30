# SCV SHA-256 text conversion overhead

Frozen source: `40ad4b3828e86f3296cf86918fa7a21ecddb195a`.
Rejected Linux producer: `9993ee84bba38cb87a7d3e296b22fa8f77fdfb12ddb5453f0047a30b05e8b35e`.
Owner reports cold SCV prime timed out at 600 seconds for 43,783 compilable files,
300,644,470 source bytes. No measurement establishes hashing as the dominant cost.

## Actual call path

Admission calls inventory refresh; each non-delete event reads source once and
calls `compile_source_inventory_event_from_content_v1`. Lines 107–113 canonicalize
once and request five digests: original content, semantic, export, initializer,
provider. The Simple facet/digest coalescing fix is a separate owned change.

`sha256_text` calls `text_to_utf8_bytes` -> `rt_text_to_bytes`, then
`sha256_u8_fast_hex` -> `rt_tls13_sha256`. Actual rejected Linux binary disassembly
contains that native provider call and the non-32-byte pure-Simple fallback.
Rust `rt_text_to_bytes` formerly pushed one tagged byte at a time into a generic
array. Rust SHA conversion then reads/type-checks/range-checks each byte into a
fresh Vec before calling `Sha256::digest`. Hex formatting allocates the digest
array and the existing Simple hexadecimal pieces. Static evidence establishes
these mechanisms, not their measured share of the timeout.

## Narrow correction

Reuse existing Rust `rt_string_bytes` exact-capacity bulk slot fill inside the
existing `rt_text_to_bytes` provider. Preserve its tagged-byte array result,
empty/invalid text behavior, and all Simple API/ABI names. No SHA algorithm or
runtime export is added. Core-C retains `rt_text_to_bytes`'s packed-byte memcpy;
a global Simple substitution with `rt_string_bytes` would instead introduce
per-byte pushes in core-C and is deliberately avoided.

Focused provider Rust tests assert exact UTF-8, embedded NUL, empty/invalid text,
and padding/block lengths. Four authored Simple scenarios and a produced-executable
fixture pin twelve SHA digests. Constants were generated once from UTF-8 bytes
using .NET SHA256 during authoring, not from the implementation under test.
Expected native stdout: `SHA256_TEXT_PROVIDER_PARITY_PASS\n`; exit 0.
All authored tests/native fixtures are NOT RUN pending high source review and
corrected qualified producer/runtime binding. No speedup or runtime PASS is claimed.

## Remaining provider parity/performance follow-up

Existing Rust exports `rt_sha256_new/write/finish/free` can hash a borrowed text
pointer/byte length without boxed conversion. They exist in rejected Linux 9993,
but core-C Windows/Linux do not provide this streaming ABI. A shared Simple facade
cannot import them until provider parity is implemented and reviewed. Existing
`rt_array_bytes_copy_checked` avoids accessor calls for packed arrays, but generic
arrays still require unboxing. Neither `rt_array_data_ptr` nor a text character
count may substitute for an exact byte slice. Defer that wider work until measured
corrected SCV prime results justify it; preserve provider compatibility and caches.

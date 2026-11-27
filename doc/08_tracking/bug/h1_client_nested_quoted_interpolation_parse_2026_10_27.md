# HTTP/1 content-encoding nested interpolation parse failure

**Date:** 2026-10-27
**Status:** Parse/HIR pass; object compile NOT PASS; runtime unqualified
**DB registration:** PENDING

## Failure evidence

The pinned all-objects Phase2 collection recorded this failure:

`D:\dev\simple-all-objects-phase2-20261027\build\object-campaign\objects\c718ec0c9fbc4f25bdfe45181b7c4bc9\11043d8c4449d80cf2244d86775919db68b922e8ef8c7c8b4795acadd06f7849\compiler.log`

It reports `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl` line
649:69: `expected ), got StringLit '}'` for the nested quoted interpolation.

## Diagnosis and repair

`find_header(headers, "content-encoding")` returns `text?`, and the existing
nil guard returns before decoding when the header is absent.
`h1_decode_content_encoding(body: [u8], header_value: text)` accepts a `text`
value. Therefore `encoding ?? ""` already has the required type and is passed
directly; this removes a redundant string interpolation without changing the
selected header value, body, or decode behavior.

The parser limitation is already documented in
[`credential_key_generate_random_hex_length_reads_shifted_2026-08-08.md`](credential_key_generate_random_hex_length_reads_shifted_2026-08-08.md#second-defect-found-while-fixing-it--nested-string-literal-inside-an-interpolation),
which records that a nested string literal inside interpolation is misparsed.
This all-objects row is a separate dated failure manifestation; DB registration
for this row is PENDING.

The direct-argument source change removes the original parse error in the
changed-input object compile. That root diagnostic completed parsing 82/82
modules and completed HIR; MIR then failed, so the object compile is **NOT
PASS** and runtime behavior remains unqualified.

## Changed-input object result

Compiler log:

`D:\dev\simple-object-repairs-luna-20261027\build\object-repair\http-h1-direct-header\compiler.log`

Receipt:

`D:\dev\simple-object-repairs-luna-20261027\build\object-repair\http-h1-direct-header\collector.sdn`

The receipt reports `reason=child-exit` and exit status 1. MIR reports later
failures including unresolved `is_empty` and unsupported non-array iteration
in `h1_client.spl` (lines 357 and 361), unsupported `Result` unwrap payloads
in `common/compress/deflate.spl`, unresolved `to_float`/`to_int` in gzip,
unresolved `append`/`to_string`/`upper` in HTTP client types, and two existing
`TextIoError.Codec` payload mismatches. These prevent object qualification;
this report does not claim runtime validation. Root owns the remaining
validation lane; no further H1 method or intrinsic workaround is proposed at
this scope.

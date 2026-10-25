# Gzip legacy helper source review — 2026-10-25

Status: **WARN — NOT_RUN**. This tracked report supersedes build/review/astra-gzip-source-review.md.

No concrete P0/P1/P2 finding identified in the frozen three-file repair. This is source review only. All three authored cases, the existing RFC suite, native LLVM/Cranelift aggregate behavior and compiler integration remain NOT_RUN. No compiler or test was launched.

Reviewed SHA256 inputs:
- src/lib/nogc_sync_mut/compression/gzip/inflate.spl:02c96f537c84c4ed87c34849dbc10a3ad99d7c7cf71190e882ecf9c7f89e7d92
- test/01_unit/lib/nogc_sync_mut/compression/gzip_inflate_negative_offset_guard_spec.spl:3b8c1023607855aac1be39eb7b1180c35e0476d2e49dacc1633a7412cccb87b8
- doc/08_tracking/bug/gzip_legacy_optional_return_inference_2026-10-25.md:b0d891dc17086ff7fce0524d0270bc5628c831d93c47c4049b17b265e436611f

The exact failed LLVM snapshot had data:[u8], offset:i64 but no return type; the same parameter-only declaration remains in fetched release source. The retained ledger identifies the synchronous family, and the asynchronous module reexports it. This repair supplies nullable input and the optional heterogeneous [Any] result, with explicit Some/nil binding before byte access. It preserves stored-block shape, marker shape, byte payloads, true/false final flags and offsets. Typing the marker's empty payload as [u8] removes element ambiguity without changing its logical value. Neighboring gzip header/footer readers already use the same nullable-input binding pattern; _inflate_core and inflate_member already declare optional heterogeneous results.

The old source-string test is replaced by production helper calls. Negative controls include nil, empty input, negative/equal-to-length/past-end offsets, truncated header and truncated payload. Stored-block assertions require all four fields, exact nonzero starting offset, payload bytes0/128/255 and next offset9. Fixed marker requires type1/finaltrue/empty byte payload/offset0; dynamic marker requires type2/finalfalse/empty byte payload/offset1. The nil arms follow explicit nonnil assertions, so they do not silently accept nil success. The existing RFC nil/stored/fixed calls remain unchanged.

The bug report correctly retains the one-module HIR failure, actual P2 producer and command, missing candidate, and absence of independently established LLVM runtime identity. It does not borrow runtime hashes or qualification from the separate Cranelift attempt. No generic inference guard or backend/authority setting was weakened. Actual optional/Any ABI and runtime compatibility remain qualification work, not established by this source review.
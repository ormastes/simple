# Phase2 native construction accepts a malformed Result/text fixture

Status: OPEN (diagnostic/type-checking follow-up, no compiler root cause claimed).

`validated_utf8_bytes_to_text_linear` returns Result<text,text>. Nil coalescing
`?? ""` is not Result payload extraction. Nevertheless, native-build construction
accepted a caller that then used the resulting value as a text receiver and
concatenation operand. Actual native observations: len=-1, bytes=[], and concat
rendered Result::Ok(...) rather than just the one-byte payload. This permitted
a misleading binary-framing test fixture. Explicit match Ok(value) yielded
len1/bytes[0] and the corrected regression passed3/0.

Reproducer source and exact output are in private
build/native_probe/traceability-text-transport-20261011/{probe.spl,observations.log}.
Construction used the authorized Rust seed only for native bootstrap compilation;
execution used the produced native binary. A full admitted compiler check has
not established whether the normal typed path already diagnoses this misuse.
Investigate the native-build type-check boundary before proposing compiler or
operator semantics changes. The intended fixture now uses explicit Result
matching; no unsupported grammar workaround or runtime repair is claimed.

# Portable PTY input UTF-8 prefix codec

**Status: authored manual; execution and docgen pending (TEST_BLOCKED).**
Source: `test/01_unit/lib/sys/pty_input_codec_spec.spl`.
Requirement: **REQ-SMUX-INPUT-002** — all eight executable scenarios carry this
trace for portable complete-UTF-8 compatibility. Native arbitrary-byte-prefix
delivery requires the separate real provider fixture and is not proven here.
All eight scenarios are unexecuted. They exercise the production pure codec;
they do not prove a PTY write, child delivery or provider fairness.

1. Encode 4095 ASCII bytes followed by a four-byte emoji. Offer the first
   4096 bytes: only 4095 complete bytes are accepted. Retry the suffix from
   that byte offset: the complete emoji is accepted without replacement.
2. End a prefix inside a two-byte or three-byte scalar. Keep the complete
   ASCII prefix and leave the unfinished trailing bytes unaccepted.
3. End after each incomplete prefix of a four-byte scalar. Trim at most three
   trailing bytes while retaining the complete prefix.
4. Offer complete two-, three- and four-byte scalars. Exact text and nine-byte
   encoded roundtrip survive.
5. Offer stray continuation bytes, invalid leading bytes or non-continuation
   bytes inside a scalar. Refuse rather than report replaced bytes as written.
6. Reject overlong sequences, UTF-16 surrogate encodings and values above
   U+10FFFF. Refuse already-invalid partial scalars instead of deferring them.
7. Empty input and a valid unfinished initial scalar accept zero bytes and
   produce no replacement text.
8. Accept explicitly encoded U+FFFD and valid encoding range endpoints.

The legacy portable PTY adapter validates this prefix and its byte roundtrip
before passing complete text to its synchronous provider. This preserves text
at bounded byte-prefix boundaries; the legacy provider still does not qualify
nonblocking owner-loop fairness. Native Windows uses its byte-preserving
configured provider directly.

Required after runtime admission:

```text
<admitted-runtime> test test/01_unit/lib/sys/pty_input_codec_spec.spl --native-backend=llvm --assert-ran --keep-artifacts
<admitted-runtime> spipe-docgen test/01_unit/lib/sys/pty_input_codec_spec.spl --output doc/06_spec --no-index
```

Record exact runtime identity and executed counts; require complete generated
documentation with zero stubs before treating this as verification evidence.

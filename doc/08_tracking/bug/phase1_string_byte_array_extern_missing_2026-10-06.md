# Phase1 string byte-array facade is not registered

The original phase2_text_method_behavior_spec.spl has four actual failing examples caused by unknown extern rt_string_to_byte_array. Its oversized-input case passes before conversion. The hosted C runtime explicitly defines this facade as a mirror of rt_text_to_bytes (src/runtime/runtime_core_io_exports.c).

Register the facade as an alias to the existing interpreter conversion::rt_text_to_bytes_fn; no duplicate converter, byte-codepoint confusion, or opaque native array handle is introduced. Two parsed-Simple interpreter regressions fail with that missing extern before the alias and pass afterward: exact UTF-8 bytes plus reverse-facade round trip, and a real empty array. Retained baseline/repaired logs and guarded receipts: /tmp/simple-string-byte-array-repair. This is repair evidence, not whole-suite or next-stage admission. Rebuilt-seed execution of the original failed budget examples remains required.

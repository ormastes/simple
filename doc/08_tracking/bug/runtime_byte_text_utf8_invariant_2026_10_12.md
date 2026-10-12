# Byte-to-text decoder violated the RuntimeString UTF-8 invariant

Status: OPEN. Source repair reviewed; runtime tests and native qualification UNEXECUTED.

`rt_bytes_to_text` accepted packed bytes and checked boxed integer bytes, then passed them directly to `rt_string_new`. Neither path established UTF-8 validity. For example, `[0x80, 0xff, 0xc3]` could become a RuntimeString despite not being UTF-8. `RuntimeString::as_str` uses `from_utf8_unchecked`, so a subsequent ordinary string operation could violate Rust's safety contract. Byte-accessor interoperability alone does not establish that invariant. This is a concrete source defect; no undefined-behavior execution is used as evidence.

The repair runs `String::from_utf8_lossy` before the constructor on both successful paths. Malformed sequences become U+FFFD, consistent with the documented lossy conversion policy in common/base_encoding.spl and the existing Rust process-output conversion. This intentionally changes malformed-input behavior; binary data must stay in byte arrays. Valid Unicode and embedded NUL are preserved. Valid input uses a borrowed Cow and adds no intermediate byte copy, although UTF-8 validation adds work. Invalid receivers and noninteger/out-of-range boxed elements still return NIL. A separate proposed nonoptional native facade maps that NIL to constructor-owned empty text; it is not added by this PR.

Three actual runtime unit tests live next to the decoder. Nine explicit malformed/truncated/overlong/surrogate/out-of-range cases and five valid Unicode/NUL/boundary cases run through both actual packed and boxed array constructors. Additional cases preserve invalid-receiver and boxed-element rejection. Assertions validate output bytes with safe `str::from_utf8` before calling string operations, so they can expose the original defect without invoking unchecked string consumers on malformed storage.

The exact source owner on the publication base matches frozen 82bba68602c2cff2b87f42b0f5ae8a54f1d14b8b. The independent seven-provider runtime attempt remains immutable and stopped at its 600-second final-link limit; no archive or native qualification is claimed. This change does not repair every raw caller of `rt_string_new` or claim that arbitrary external input to that constructor is safe.

Validation command, from the isolated src/compiler_rust workspace:

    cargo test --locked --profile bootstrap --package simple-runtime --lib --jobs 2 --target-dir <owned-target> byte_text_utf8_invariant_tests -- --test-threads=1

This command has not been run. Matched native-all feature/archive construction, Windows heap/ABI fixtures, throughput checks, and required compiler/core/lib/MCP gates remain open. No capped Simple build is restarted. Valid-input allocation preservation is a source observation, not a performance PASS.

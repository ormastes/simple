# BUG: x86_64 freestanding — `char_code_at` mis-decodes on dynamically-built text

## Status
Source fixed; current-source freestanding QEMU proof pending. Found 2026-07-12
(Phase 2e Inc 2). Distinct from the frame-depth-sensitive
`starts_with` bug in `x64_freestanding_text_char_at_starts_with.md` §Status point 3.
Worked around at the call site with the `[u8]` byte-array idiom.

## Summary
On the x86_64 freestanding native-build (cranelift, `--target x86_64-unknown-none`),
`text.char_code_at(i)` returns garbage / boxed-object values at scattered indices
**when `text` is a DYNAMICALLY built string** (e.g. produced by
`rt_string_from_byte_array` at runtime — exactly what a decoded SSH command is).

- A rodata string LITERAL iterates correctly with `char_code_at`.
- A heap-built `text` does NOT — scattered indices return wrong codes.
- Reproduces at the SHALLOWEST possible frame (bare `_start()`), so it is NOT the
  frame-depth / stack-spill `starts_with` bug; it is a distinct per-char accessor
  codegen bug specific to heap-built text.

## Repro
`examples/09_embedded/simple_os/arch/x86_64/clang_argv_tokenize_probe_entry.spl` +
`scripts/os/clang_argv_tokenize_probe_run.shs` — builds a text via
`rt_string_from_byte_array`, iterates it with `char_code_at`, and prints the codes
(garbage) vs the `[u8]`-idiom codes (correct). ~6 s boot vs ~5 min for the SSH kernel.

## Workaround (in use)
Convert the dynamic `text` to a byte array ONCE and index the bytes, never
`char_code_at` on the text directly:
`rt_string_to_byte_array(s)` + `rt_bytes_u8_at(bytes, i)`. See
`_sshd_tokenize_command` in `src/os/apps/sshd/sshd.spl`.

## Fix (root)
Fix the cranelift lowering of `char_code_at` (string index → raw code) so it
handles a heap-built text handle the same as a rodata literal. Likely the same
tag/handle-dereference area as the other freestanding text-op bugs; compare the
LLVM backend path (correct). Add the probe above as a regression gate once fixed.

Pure-Simple MIR now emits a reserved alias of the existing runtime helper after
custom-owner dispatch and preserves its raw i64 result. The helper itself owns raw-versus-
tagged text normalization without allocation, so concat-built heap text and
rodata literals share one path. LLVM/Cranelift plus hosted/AArch64/RV64 fixtures
pin the ABI and Unicode character indexing. Keep the call-site byte-array
workaround until the original x86_64 QEMU probe passes with a rebuilt
pure-Simple compiler.

## Related
- `doc/08_tracking/bug/x64_freestanding_text_char_at_starts_with.md`
- `doc/08_tracking/bug/x64_freestanding_rt_string_to_int_stub.md`

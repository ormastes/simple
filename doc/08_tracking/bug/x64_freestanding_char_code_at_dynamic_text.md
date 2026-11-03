# BUG: x86_64 freestanding — `char_code_at` mis-decodes on dynamically-built text
## Closed 2026-09-16 — ...` in `src/os/apps/sshd/sshd.spl`. ## Fix (root) Fix the cranelift lowering of `char_code_a

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Status
Open. Found 2026-07-12 (Phase 2e Inc 2). Distinct from the frame-depth-sensitive
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

## Related
- `doc/08_tracking/bug/x64_freestanding_text_char_at_starts_with.md`
- `doc/08_tracking/bug/x64_freestanding_rt_string_to_int_stub.md`

**Revalidated 2026-11-02: still plausible because the report title (x86_64 freestanding char_code_at mis-decodes at scattered indices on dynamicall) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## Fix 2026-11-03 (fix-implemented, verification-pending)
Root cause in the freestanding runtime, not cranelift:
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`
`rt_string_char_code_at` was BYTE-indexed (hosted `runtime_native.c` and the
aarch64 freestanding runtime are CODEPOINT-indexed UTF-8), and the compiled-lane
symbols `__simple_rt_string_char_code_at`, `rt_string_byte_at`,
`__simple_rt_string_byte_at` were missing on x86_64. Now: no-alloc decoder in
`x86_64_text_codepoint.h`, used by `rt_string_char_code_at`, tagged
`char_code_at`, and the new byte_at / `__simple_*` aliases.
Siblings checked: `rt_string_len` and `rt_string_char_at` are byte-based on the
hosted runtime too — consistent, no gap.

Evidence (Windows, no QEMU):
- `clang -std=c11 -Wall -Werror -Iexamples/09_embedded/simple_os/arch/x86_64/boot test/01_unit/runtime/x86_64_freestanding_char_code_at_test.c -o t && ./t` -> PASS (fails to build before the fix).
- `clang --target=x86_64-unknown-none -ffreestanding -fno-builtin -nostdlib -mno-red-zone -O1 -c baremetal_stubs.c` + `llvm-nm` -> all five symbols `T`.

QEMU steps still owed (not run): `sh scripts/os/clang_argv_tokenize_probe_run.shs`
on the real-firmware lane; the `char_code_at` codes must equal the `[u8]`-idiom
codes. Then drop the `[u8]` workaround in `_sshd_tokenize_command`.

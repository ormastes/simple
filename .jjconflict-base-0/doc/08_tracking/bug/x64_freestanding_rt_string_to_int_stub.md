# BUG: x86_64 freestanding — `rt_string_to_int` is a hardcoded stub returning 0

## Status
Open. Found 2026-07-12 while root-causing the SSH command-decode bug (Phase 2e).
Not yet fixed; low blast radius today but a real correctness hole.

## Summary
On the x86_64 freestanding native-build (SimpleOS kernels), `rt_string_to_int`
(`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:8045`) is a
hardcoded stub that ALWAYS returns 0. Any freestanding code calling
`text.to_i64()` / `text.to_int()` silently gets 0 instead of the parsed integer.

## Impact
- Any numeric parse from a `text` in freestanding code is wrong (silently 0).
- Concrete misuse observed: `_ssh_identification_text_to_bytes_stable`
  (`src/os/apps/sshd/ssh_session.spl:99-105`) uses it for byte extraction, so it
  relies on the 0 return by accident rather than parsing.
- Not currently on the clang-over-SSH happy path (that path avoids `.to_i64()`),
  so it did not block Phase 2e — but it will bite any freestanding feature that
  parses integers from text (config values, decimal args, etc.).

## Fix
Implement `rt_string_to_int` for real: parse an optionally-signed base-10 integer
from the `text` (mirror the hosted runtime's `rt_string_to_int` / the `_digit_val`
approach already used elsewhere in `baremetal_stubs.c`), returning the parsed i64.
Add a shallow freestanding probe (like
`text_char_at_store_probe_entry.spl`) asserting `"42".to_i64() == 42` and a
negative/whitespace case.

## Related
- `doc/08_tracking/bug/x64_freestanding_text_char_at_starts_with.md` (sibling
  freestanding text-op corrections; §Status point 3 = the deep-stack `starts_with`
  bug, still open)

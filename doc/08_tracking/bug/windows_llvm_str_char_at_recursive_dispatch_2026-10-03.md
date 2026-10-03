# Windows LLVM character helper recursive dispatch

Status: focused native repair PASS; full compiler qualification pending.

On source `43f626850b6a5531e89110f75cd1eaedc24adcd1`, a 55-module LLVM
bootstrap diagnostic compiled successfully, then timed out after 120 seconds
while preparing an empty environment policy. The first five byte conversion
and UTF-8 checks completed. The policy collection completed; handoff construction
did not. The executable used approximately 5.4 MB RSS while consuming a CPU.

Five bounded Windows thread-context samples all identified PE RVA `0x30090`.
The retained `string_core` object identifies that instruction as `str_char_at`
plus `0x10`: bytes `eb fe`, an unconditional jump to itself. The helper's
`s.char_at(idx)` dispatch resolves back to `str_char_at`; LLVM optimizes the
tail recursion into an infinite loop. Policy hexadecimal encoding calls this
helper for every digit. This is a concrete native timeout cause, independent
of the earlier expensive source inventory publication.

The repair implements Unicode scalar indexing directly in the helper by
walking UTF-8 byte boundaries and slicing one complete scalar. Negative and
out-of-range ordinals return empty text. It creates no temporary byte arrays,
uses no unsafe handles, and does not redispatch the character method.

Focused fixtures cover ASCII, two/three/four-byte scalars, empty text, negative
and out-of-range indices, byte conversion, malformed/truncated UTF-8 rejection,
and empty policy encoding. The separate byte-copy repair used by the fixture
belongs to `windows_policy_handoff_linear_byte_copy_2026-10-03.md`.

Retained Windows evidence:

- `C:/Users/user/.simple/worktrees/simple-windows-phase2/build/native_probe/llvm-policy-codec-repair1`: 55 compiled, zero cached/failed; execution timeout.
- `C:/Users/user/.simple/worktrees/simple-windows-phase2/build/native_probe/llvm-policy-codec-repair2`: phase markers, `ip-samples.json`, execution timeout with clean reaping.
- `C:/Users/user/.simple/worktrees/simple-windows-phase2/build/native_probe/llvm-policy-codec-repair3`: repaired source, 40 requested build workers, 55 compiled / zero cached / zero failed, 14 focused oracles with zero failures and raw exit zero. Empty policy payload length is 1,884 bytes. Build peak RSS is 1,548,520 KiB under the enforced 5,859,375 KiB process-tree cap; quiescent receipt is present.

The original 1,200-second LLVM qualification remains failed and unchanged.
This diagnostic does not admit a compiler, qualify the full frontend, or
replace compiler/interpreter/loader test execution.

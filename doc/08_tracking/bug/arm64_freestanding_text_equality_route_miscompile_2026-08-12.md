# ARM64 Freestanding Text Equality Route Miscompile

**Date:** 2026-08-12  
**Status:** Workaround implemented; compiler root cause open

The ARM64 filesystem-exec guest printed the canonical mapped text
`/QEMUNONC.TXT`, but the immediately following Simple equality branch did not
match it. Earlier retained builds similarly sent exact root paths through an
unrelated prefix route. Live5 serial SHA-256 is
`d8a01ace56a113aee455b2986717c00b158a999eb81cec74f068d5d3a205343b`.

This is positive evidence of incorrect freestanding text equality/match
lowering, not merely an alias-table omission: the mapped value is printed from
the same call frame before the missed exact branch, and a real-image regression
proves the FAT dirent exists.

The VFS workaround moves path classification into the typed ARM64 C ABI owner.
It compares exact runtime-string length and bytes and returns a closed raw code
for the four allowed root files plus `/SYS/APPS/` and `/SYS/` descendants.
Near-case, trailing bytes, embedded NUL, directory-only prefixes, unknown root
names, and alias-shaped inputs are rejected. The Simple route contains no text
equality, match, or prefix operation.

Compiler follow-up should add a minimal ARM64 freestanding executable that
constructs/returns a heap text across a function boundary and checks exact
equality, match arms, and prefix behavior against literals. Do not remove the
typed classifier until that target-level regression passes.

## Live8 storage-domain result

One strict build and one TCG boot with the tagged/raw bump-heap validator still
returned route 0 for visibly canonical `/QEMUNONC.TXT`. This disproves the
specific hypothesis that the extern argument is a raw `RuntimeString*` inside
the used bump heap. The value is likely a static/rodata string object or a
different raw text ABI form already accepted by ARM64 printing.

Before changing validation, inspect the retained live8 classifier call-site
and wrapper disassembly plus the existing print-path raw-text decoder. Any next
decoder must validate a precise kernel image/rodata range and object layout;
do not accept arbitrary host/physical pointers or fall back by path intent.
Evidence is retained at
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/arm64-real-el0-20260812T-live8/`,
serial SHA-256
`a5ea4103ac7e9761fb0beeef092cc5f846da8bc5bd42576dc367defd19af30bb`.

## Live6 construction blocker

The first bounded build after introducing the classifier stopped at strict
codegen before linking. `route` was accidentally declared in
`arm_fs_exec_read_file_bytes` rather than `_arm_fat32_read_path_from_dev`, whose
body uses it. Strict no-stub fallback correctly rejected the unresolved local.
No kernel/image receipt or nonce media was produced and QEMU attempts were
zero. Evidence is retained at
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/arm64-real-el0-20260812T-live6/`.
This is an integration placement error, not evidence against the C classifier.

## Live7 classifier input ABI blocker

After correcting local placement, one strict build and one TCG boot completed.
VFS reached ready and printed mapped `/QEMUNONC.TXT`, but the typed classifier
returned the reject code 0 before any root scan. The wrapper currently calls
`decode_string`, which accepts only tagged heap values. Other ARM64 runtime
owners explicitly support both tagged heap strings and validated raw
`RuntimeString*` values; the observed behavior is consistent with this extern
receiving the latter. The next source repair must decode both representations
with heap-range/header/length validation before invoking the byte classifier.
Do not weaken exact-byte matching or add a route fallback.

Retained evidence:
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/arm64-real-el0-20260812T-live7/`,
serial SHA-256
`a6b2c175509fe248bf568d093d47b4d661987eb4d14096bc98d7929be87e64f0`.
Nonce, listing, EL0 stdout, exit 37, resume/reap, and TEST PASSED remain absent.

### Tagged/raw RuntimeString decoder hardening

The classifier wrapper now normalizes either a tag-1 heap value or a raw
pointer, then validates the candidate against the used ARM64 bump-heap range.
It requires a complete runtime-string header, `HEAP_STRING`, length at most
4096, overflow-safe containment of `header + bytes + terminal`, a sufficiently
large object-size field, and an exact terminal NUL before classifying bytes.

The executable C sabotage proves tagged/raw parity for `/QEMUNONC.TXT` and
rejects below/above-heap pointers, wrong object type, oversized length,
truncated object size, missing terminal NUL, and embedded NUL. The exact route
classifier itself is unchanged. AArch64 freestanding syntax and diff checks
pass. No rebuild or QEMU run accompanied this source repair.
## Live8 retained-binary ABI diagnosis (2026-08-12)

The retained live8 kernel falsifies the proposed static/rodata RuntimeString
explanation for route `0`:

- `rt_string_new_literal` at `0x4020962c` forwards `(rodata_bytes, length)` to
  `rt_string_new` at `0x40201aac`.
- `rt_string_new` allocates `sizeof(RuntimeString) + length + 1` through
  `_heap_alloc`, writes `{type=1, size, len, data, NUL}`, and returns the
  16-byte-aligned object pointer tagged with bit zero.
- `_arm_exec_alias` constructs every returned alias through that function.
  `_arm_fat32_read_path_from_dev` stores the returned `x0`, leaves it unchanged,
  and calls `rt_arm_fs_path_route` indirectly at `0x40242dbc`.
- The runtime bump heap is exactly `0x4024b440..0x4a24b440`; `_heap_off` is the
  word at `0x4a24b440`. The wrapper loads that word and validates against the
  used prefix of this range.

The addresses in `.rodata` are only untagged source byte arrays accompanied by
an explicit length in `x1`; they are not self-describing RuntimeString objects
and cannot be decoded safely from the wrapper's single `RuntimeValue` argument.
Consequently the classifier must **not** accept arbitrary load-image/rodata
addresses as strings. Such a change would broaden the trusted pointer range,
would admit forged headers in immutable image data, and would not accept the
actual value produced at this call site. The remaining route failure is after
canonical literal construction and requires value/rejection-reason capture at
the wrapper boundary in a later live diagnostic.

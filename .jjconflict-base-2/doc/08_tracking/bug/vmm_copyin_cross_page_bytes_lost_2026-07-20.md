# vmm_copyin_bytes_from_space returns empty `bytes` when a copy crosses two mapped pages

**Status:** Open
**Category:** GENUINE-BUG (interpreter/runtime — nested-loop array accumulation)
**Discovered:** 2026-07-20 (whole-suite triage campaign, shard meas_01u_03)

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/os/kernel/memory/vmm_copyin_spec.spl --no-session-daemon
```

```
  ✓ rejects cross-page read ranges when the tail page cannot translate
  ✓ rejects write ranges without writable PTE access
  ✓ copy-in reports EFAULT instead of dereferencing when translation misses
  ✗ copies a byte range that crosses two mapped readable pages
    semantic: array index out of bounds: index is 0 but length is 0
  ✓ rejects cross-page copy when the tail page is unmapped

7 examples, 1 failure
```

## Minimal repro

`test/01_unit/os/kernel/memory/vmm_copyin_spec.spl` lines 140-163 (unedited,
sole failing `it`):
```
it "copies a byte range that crosses two mapped readable pages":
    vmm_copy_clear_test_words()
    val pml4: u64 = 0x100000
    val pdpt: u64 = 0x101000
    val pd: u64 = 0x102000
    val pt: u64 = 0x103000
    val data0: u64 = 0x104000
    val data1: u64 = 0x105000
    _wire_test_user_pages(pml4, pdpt, pd, pt, 0x7000, data0, data1)
    vmm_copy_set_test_word(data0 + 0xFF0, 0x4746454443424140)
    vmm_copy_set_test_word(data0 + 0xFF8, 0x4F4E4D4C4B4A4948)
    vmm_copy_set_test_word(data1, 0x6766656463626160)
    vmm_copy_set_test_word(data1 + 8, 0x6F6E6D6C6B6A6968)
    val area = VmArea(start: 0x7000, len: 8192, kind: VMA_ANON, flags: VMA_READ, backing: 0, backing_offset: 0)
    var space = ProcessVmSpace(pml4: pml4, id: 6, vma_count: 0, areas: [])
    space.vma_count = 1
    space.areas.push(area)
    val result = vmm_copyin_bytes_from_space(space, 0x7FF0, 32)
    expect(result.status.ok).to_equal(true)
    expect(result.bytes.len()).to_equal(32)     # <-- fails: len is 0
    expect(result.bytes[0]).to_equal(0x40u8)    # <-- index-out-of-bounds on empty array
    ...
```

`result.status.ok` is presumably `true` (the harness didn't stop earlier), but
`result.bytes` comes back with length 0 instead of the expected 32 bytes —
`result.bytes[0]` then throws `array index out of bounds: index is 0 but
length is 0`.

## Implementation under test

`src/os/kernel/memory/vmm_copy.spl:255-289`:
```
fn vmm_copyin_bytes_from_space(space: ProcessVmSpace, ptr: u64, len: u64) -> VmmCopyBytesResult:
    """Copy an exact byte range through an explicit address-space page walk."""
    if ptr == 0:
        return _vmm_copy_bytes_err(14)
    if len == 0:
        return VmmCopyBytesResult(status: _vmm_copy_ok(0), bytes: [])
    if ptr + len < ptr:
        return _vmm_copy_bytes_err(14)
    if not vmm_pt_range_user_readable(space, ptr, len):
        return _vmm_copy_bytes_err(14)

    var bytes: [u8] = []
    var copied: u64 = 0
    while copied < len:
        val current = ptr + copied
        if space.vma_count > 0:
            val area = vma_find(space, current)
            if area == nil:
                return _vmm_copy_bytes_err(14)
            if (area.flags & 1) == 0:
                return _vmm_copy_bytes_err(14)
        val walked = _vmm_pt_walk(space, current, PTE_PRESENT | PTE_USER)
        if not walked.ok:
            return _vmm_copy_bytes_err(14)
        var chunk = walked.bytes_until_page_end
        val remaining = len - copied
        if chunk > remaining:
            chunk = remaining
        var i: u64 = 0
        while i < chunk:
            bytes.push(_vmm_read_physmap_byte(walked.kernel_ptr + i))
            i = i + 1
        copied = copied + chunk

    VmmCopyBytesResult(status: _vmm_copy_ok(len), bytes: bytes)
```

## Root-cause hypothesis

The distinguishing feature of this test versus the 3 adjacent passing tests
(which either single-page-copy or take an early-return error path before
ever pushing to `bytes`) is that it is the only case that walks **two page
iterations of the outer `while copied < len` loop**, each pushing multiple
elements via a **nested inner `while i < chunk: bytes.push(...)`** loop onto
an outer-scope `var bytes: [u8] = []`.

Per project-known array semantics (arrays are value types, passed by copy;
mutation must go through the same-scope variable or a helper), `bytes.push`
inside a loop nested two levels deep, across two outer-loop iterations, and
finally returned via `VmmCopyBytesResult(..., bytes: bytes)` at the very end
of the function, appears to lose the accumulated pushes — the returned
`bytes` field is empty (len 0) rather than containing the 32 accumulated
bytes. This looks like the interpreter is not correctly threading the
mutated `[u8]` value out of the nested-while/outer-while control flow before
the final struct-construction expression reads it — i.e. a genuine
array-mutation-across-nested-loop-scopes interpreter defect, not a logic bug
in the kernel code itself (the algorithm is correct: single-page and
early-return-error paths all pass).

## Why not classified STALE-TEST

The assertions (`result.bytes.len()).to_equal(32)`, exact byte values at
indices 0/15/16/31 spanning both pages) are correct expectations of a
byte-copy-across-pages function and must not be weakened. No API rename or
migration applies — `vmm_copyin_bytes_from_space` is the current, only
implementation.

## Affected specs

- `test/01_unit/os/kernel/memory/vmm_copyin_spec.spl` (1 of 7 examples: "copies a byte range that crosses two mapped readable pages")

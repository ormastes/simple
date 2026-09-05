# do_version_exchange "chained cast / rt_bytes_slice" note — NOT A BUG (verified)

**Target:** `native-build --backend cranelift --target x86_64-unknown-none`
(SimpleOS freestanding). **Status:** RESOLVED / NOT REPRODUCIBLE. Filed as its
own record because a code comment in `do_version_exchange`
(`src/os/apps/sshd/ssh_session.spl`) long asserted a compiler bug here, and the
claim propagated into other notes. Kept so it is not re-investigated.

## The note (both halves) and how each was tested

`do_version_exchange` builds the server banner via
`ssh_build_version_string() -> [u8]` and had a NOTE claiming two x64-freestanding
codegen defects:

- **(a)** `our_version.len().to_i64()` (chained cast) mis-lowers and yields garbage.
- **(b)** storing an `rt_bytes_slice` extern-`[u8]` return DIRECTLY into a struct
  field drops the BYTE_PACKED representation, so it must go through
  `_copy_bytes_stable`.

A faithful freestanding probe (`arr: [u8]` built with `.push`;
`rt_bytes_slice(arr: [u8], start: i64, length: i64) -> [u8]` — the REAL
signature) booted under QEMU showed **both are false**:

- chained `arr.len().to_i64() - 2` == the bound form == **19**;
- `rt_bytes_slice(arr, 0, 19)` used directly → `len=19`, `[0]=83` (`'S'`);
- stored **directly into a struct field** (no `_copy_bytes_stable`) →
  `len=19`, `[0]=83`.

## Caution (the false-positive that nearly got this mis-filed)

An intermediate probe declared the extern with the WRONG signature
(`rt_bytes_slice(s: text, ..)` instead of `(arr: [u8], ..)`) and passed a `text`.
Passing a text handle where a `[u8]` handle is expected returned garbage
(`len=1153202240580805315`, bytes `0`) — a **probe artifact**, not a codegen bug.
Always match the real extern signature before concluding.

## Disposition

The `ov_len` bind and the `_copy_bytes_stable` wrapper in `do_version_exchange`
are harmless defensive copies, NOT workarounds for a real bug, and were left in
place (no logic change to the SSH version-exchange critical path). This is part
of the same arc as the retracted
`x64_freestanding_chained_len_cast_miscompile.md`; the ONE genuine defect from
that arc is the `rt_push_byte` reassignment dropping BYTE_PACKED for large `[u8]`
(`x64_freestanding_push_byte_reassign_byte_packed.md`, fixed with `.push`).

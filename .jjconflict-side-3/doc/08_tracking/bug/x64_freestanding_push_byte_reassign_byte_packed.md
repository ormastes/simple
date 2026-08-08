# ROOT CAUSE FOUND: `u8.to_i64()` mis-dispatches to `VfsFileSize.to_i64()` (method-name collision)

**Target:** `native-build --backend cranelift --target x86_64-unknown-none`
(SimpleOS freestanding). **Status:** ROOT-CAUSED via asm dump. NOT a backend
codegen bug and NOT "reassignment drops BYTE_PACKED" — it is a FRONTEND
method-resolution collision. Workaround (`.push`) landed and verified.

## Root cause (proven by disassembly)

`objdump` of `_build_channel_data_stable` in the miscompiled (reassignment) scp
kernel shows the data loop's `_u8_at(data,i).to_i64()` compiles to:
```
call _u8_at                      # -> u8 byte in rax   (0x1ba033)
call services__vfs__vfs_boot_init__VfsFileSize.to_i64   # (0x274902)  <-- WRONG
call rt_push_byte(payload, rax)  # (0x1277b0)
```
`_u8_at` returns `u8`; its `.to_i64()` should be the primitive u8→i64 conversion.
Instead it bound to `VfsFileSize.to_i64()` (`src/os/services/vfs/vfs_boot_init.spl:77`,
`me fn to_i64() -> i64: self.bytes`). That method treats the small byte value
(0-255) as a `VfsFileSize` pointer and returns `self.bytes` (a field load off a
tiny address) → garbage (the `0x53` fill). This is a `to_i64` method-NAME
collision: the resolver picked the user-class method over the primitive
conversion.

## Why every earlier observation fits

- `.push(_u8_at(data,i))` is correct because it takes the `u8` directly — there
  is no `.to_i64()` to mis-resolve. (Not because reassignment is unsafe.)
- The three standalone probes PASSED because their entry-closure did not pull in
  `services.vfs.vfs_boot_init.VfsFileSize`, so `.to_i64()` resolved to the
  primitive conversion. The full sshd/OS closure DOES include `VfsFileSize`,
  which is exactly why the bug is "context-dependent."
- Real-code revert reproduced the `0x53` garbage (sha `f496977c`); `.push`
  restores byte-exact (`d0c481d8`).

## The actual fix belongs in method resolution

Primitive `.to_i64()` (u8/i32/… → i64) must not be shadowed by a same-named
user-class method (`to_i64`) that happens to be in the module closure. Fix in the
HIR/type-check method resolver (receiver-type-strict dispatch), NOT the cranelift
backend. A same-name-collision hazard is already noted for the interpreter
(global method registry); this is the native-codegen analogue.

## Symptom (in the real code)

`_build_channel_data_stable` in `src/os/apps/sshd/ssh_session.spl` built the SSH
channel-data payload with `payload = rt_push_byte(payload, _u8_at(data,i).to_i64())`
in a loop. A 712-byte `getfile /hello.o` response was delivered as `0x53`-garbage
(`7c9a419a5353…`, sha `f496977c…`) while small handshake/exit packets from the
same builder delivered fine — which is why the SSH session worked and masked it.
Switching the data loop to `payload.push(_u8_at(data,i))` made the delivered object
BYTE-IDENTICAL to disk (sha256 `d0c481d8…90a8c39b`, host-links + runs == exit 7).
Landed `cd0418ee39cb`.

## Proof it is REAL (real-code revert)

Reverting ONLY the data loop back to the `rt_push_byte(..)` reassignment +
`.to_i64()` form (`.push` → reassignment), rebuilding the scp kernel, and rerunning
getfile reproduced the exact `0x53`-garbage (`f496977c…`). Restoring `.push`
restores byte-exact. So the `.push` fix is genuine and the reassignment form is the
trigger IN THIS CONTEXT — not a coincidence.

## …but NOT minimally reproducible — three probes all PASSED

Faithful freestanding probes (`pushbyte_probe_entry.spl`, booted under QEMU) could
NOT reproduce the corruption. All read back CORRECT content at 712 bytes:
1. reassignment build (small header + 712-byte data loop), content via native index;
2. same, reading via `_u8_at` (`rt_bytes_u8_at(..).to_u8()` extern) instead of index;
3. the EXACT real expression — `data` itself reassignment-built, read via
   `_u8_at(data,i).to_i64()` (the double-cast on the extern u8 return), reassign-built
   `payload`. All → correct.

So plain "reassignment drops BYTE_PACKED for large arrays" is NOT the mechanism
(that form works in isolation). The corruption emerges only in the full sshd frame
— deep call stack, high register pressure, and interaction with live session/cipher
state — which a standalone entry does not reproduce. A cranelift-lowering fix needs
a repro that captures that context; it has not been found.

## What was ruled out this arc (all disproven by repro)

- chained `x.len().to_u32()` mis-lowering (retracted;
  `x64_freestanding_chained_len_cast_miscompile.md`);
- non-persisting nested-`me` mutation;
- the `do_version_exchange` chained-cast / rt_bytes_slice note
  (`x64_freestanding_do_version_exchange_note_not_a_bug.md`);
- plain `rt_push_byte` reassignment and the `_u8_at(..).to_i64()` extern double-cast
  in isolation (this doc).

The ONE confirmed-real defect is the context-dependent corruption above; the pragmatic,
verified fix is `.push` at the call site.

## Related

`_copy_bytes_stable` (`ssh_session_helpers.spl`) already documents this hazard
and uses `.push` deliberately — the general fix is to make the
extern-`[u8]`-return-into-`[u8]`-local reassignment preserve the packed
representation in the cranelift lowering, so `rt_push_byte`-style helpers are
safe again. The separately-retracted
`x64_freestanding_chained_len_cast_miscompile.md` was a mis-attribution of THIS
corruption to a chained cast.

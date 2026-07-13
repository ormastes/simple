# x64 freestanding: `rt_push_byte` reassignment corrupts a large [u8] — REAL but not minimally reproducible

**Target:** `native-build --backend cranelift --target x86_64-unknown-none`
(SimpleOS freestanding). **Status:** OPEN, workaround landed. The bug is REAL
(confirmed by a real-code revert, below) but is NOT reproducible in isolation, so
the cranelift-lowering root cause is NOT yet located. Do NOT attempt a backend
patch until a minimal repro exists — three faithful probes could not produce one.

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

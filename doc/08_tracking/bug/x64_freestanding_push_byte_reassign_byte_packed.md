# x64 freestanding: `x = rt_push_byte(x, ..)` reassignment drops BYTE_PACKED for large [u8]

**Target:** `native-build --backend cranelift --target x86_64-unknown-none`
(SimpleOS freestanding). **Status:** OPEN (worked around with the `.push`
intrinsic at the affected call site; a proper fix belongs in the codegen for the
extern-`[u8]`-return-into-local reassignment).

## Symptom

Building a `[u8]` with the extern reassignment form —
`payload = rt_push_byte(payload, b)` in a loop — corrupts the buffer once it
grows large: the elements read back wrong (dominated by a fixed byte, `0x53` in
the observed case) even though each pushed value was correct. Small arrays
(tens of bytes) are fine — they stay inline-packed — so the corruption only
shows past the inline-packed threshold. The intrinsic `x.push(b)` form (mutates
in place, preserves the BYTE_PACKED contract) is correct at all sizes.

```
# BROKEN on x64 freestanding for large arrays — drops BYTE_PACKED:
while i < data.len():
    payload = rt_push_byte(payload, _u8_at(data, i).to_i64())
    i = i + 1
# CORRECT — .push mutates in place, keeps packing:
while i < data.len():
    payload.push(_u8_at(data, i))
    i = i + 1
```

## Confirmed instance

`_build_channel_data_stable` in `src/os/apps/sshd/ssh_session.spl` built the SSH
channel-data payload with the reassignment form. A 712-byte `getfile /hello.o`
response was delivered as `0x53`-garbage while small handshake/exit-status
packets (same builder) delivered fine — which is why the SSH session itself
worked and masked the bug. Switching the data loop to `.push` made the delivered
object BYTE-IDENTICAL to the on-disk file (sha256 `d0c481d8…90a8c39b`, host-links
+ runs == exit 7). Landed `cd0418ee39cb`.

## Related

`_copy_bytes_stable` (`ssh_session_helpers.spl`) already documents this hazard
and uses `.push` deliberately — the general fix is to make the
extern-`[u8]`-return-into-`[u8]`-local reassignment preserve the packed
representation in the cranelift lowering, so `rt_push_byte`-style helpers are
safe again. The separately-retracted
`x64_freestanding_chained_len_cast_miscompile.md` was a mis-attribution of THIS
corruption to a chained cast.

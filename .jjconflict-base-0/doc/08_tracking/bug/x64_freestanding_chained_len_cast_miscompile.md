# x64 freestanding: chained `x.len().to_u32()` — NOT A BUG (retracted)

**Status:** RESOLVED / NOT REPRODUCIBLE. This file previously claimed a cranelift
backend mis-lowering of a cast chained onto a call result
(`x.len().to_u32()` / `.to_i64()`) on `--target x86_64-unknown-none`. That claim
was WRONG. Kept as a record so the phantom is not re-investigated.

## What was actually checked

- **Three standalone freestanding probes** (`chained_cast_probe_entry.spl`,
  booted via `scripts/os/chained_cast_probe.shs`) — a plain `[u8]` local, a
  `[u8]` function parameter with `len()` called twice inside an `and`, the cast
  as a call argument, arrays of 3 and 712 elements, and a `me` method on a
  multi-field struct under register pressure. **Every variant printed the
  correct value** (`chained == bound`); none reproduced a mis-lowering.
- **Real-code revert.** `_finish_exec_request_inline` was reverted from the
  bound `out_len` form back to `output.len().to_u32()` chained; the getfile
  retrieval STILL delivered `/hello.o` **byte-identical** to the on-disk file
  (sha256 `d0c481d8…90a8c39b`). So the bind was never necessary.

## The real defect (this is what actually broke Inc 3)

`_build_channel_data_stable` copied the channel payload with the
`payload = rt_push_byte(payload, ..)` REASSIGNMENT form, which on x86_64
freestanding drops the BYTE_PACKED representation once the array grows large and
corrupts the payload (the 712-byte object was delivered as 0x53-garbage; small
handshake packets stayed inline-packed and delivered fine, masking it). Switching
the data loop to the `.push` intrinsic fixed it — byte-identity confirmed. See
`x64_freestanding_push_byte_reassign_byte_packed.md` and the `_copy_bytes_stable`
note in `src/os/apps/sshd/ssh_session_helpers.spl`.

## Related: the `do_version_exchange` note (also verified NOT a bug)

The pre-existing `do_version_exchange` note (chained `[u8].len().to_i64()` +
`rt_bytes_slice` extern-return-into-field) was investigated separately and is
ALSO false — see
`x64_freestanding_do_version_exchange_note_not_a_bug.md`.

## Open thread

- One thing remains unexplained (not chased, superseded): the very first getfile
  boot produced an EMPTY object (0 bytes) rather than 712-of-garbage; the likely
  cause is a transient/reconnect, not a chained cast. The endpoint is byte-exact.

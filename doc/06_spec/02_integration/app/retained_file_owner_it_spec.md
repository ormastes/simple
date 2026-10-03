# Retained file sequential ownership

Source: `test/02_integration/app/retained_file_owner_it_spec.spl`.
Evidence: **UNRUN**. Manually authored intent mirror; no docgen, native runtime,
coverage or host qualification has been observed.

1. Create an actual exclusive native file. Write two chunks through the same
   mutable owner and check cumulative position/size. Reject a quota excess;
   close invalidates its handle. Repeated close must leave a later native owner
   usable. Reopen and verify exact binary bytes and final identity.
2. Read two bytes sequentially, read the first two bytes positionally, then read
   the remaining bytes through the original owner. Check logical position and
   EOF without losing or duplicating bytes. Reject reads after close.
3. Request three bytes from a two-byte file. Exact read must fail with truncation
   while preserving the consumed position. Zero-byte reads succeed; negative or
   oversized exact records fail without further cursor progress.

All setup uses real temporary files. No fake native handles or simulated I/O
results substitute for production operations. Partial native write failure is
source-reviewed (state advances per completed chunk), not fault-injection proven.

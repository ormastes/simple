# SOSIX service positioned backend v1

This executable specification defines the integration boundary between an
authenticated pointer-free filesystem plan and lower-layer positioned I/O.

## Required backend contract

`SosixPositionedVfsBackendV1` must implement `read_at` and `write_at` without
reading or changing a shared open-file-description cursor. A seek/read/restore
sequence does not satisfy this contract because another request can race it.

## Successful adapter flows

The focused fixture implements direct offset indexing with no cursor state. A
READ_AT copies bytes 30, 40, and 50 into registered buffer 1300. A WRITE_AT
persists registered bytes 71, 72, and 73 at absolute offset 2.

## Current canonical VFS limitation

The current `Filesystem` trait exposes cursor-based `read`, `write`, and
`seek`, but no atomic positioned operation. Production adapters must therefore
report `positioned_io_available() == false` until their driver and mount path
provide genuine positioned I/O. Dispatch then returns status -38 and reason
`backend-positioned-io-unavailable`; it performs no I/O and transfers zero
bytes.

Unaccepted plans, mismatched registrations, and out-of-range registered-buffer
access also fail before the backend is called. No API accepts a raw address.

## Hostile backend postconditions

The service does not trust a backend merely because it implements the trait.
If `read_at` returns more bytes than the authenticated plan length, dispatch
returns `backend-read-exceeds-request` before copying any byte into the
registered buffer. If `write_at` reports more transferred bytes than supplied,
dispatch returns `backend-write-exceeds-request` with zero accepted progress.
Focused sabotage fixtures exercise both impossible responses.

# SOSIX FS v1 Client Adapter

Source: `test/01_unit/os/sosix/fs_client_adapter_v1_spec.spl`

The client planner accepts only typed, generation-bearing file capabilities
and registered buffers. It validates the reply endpoint and request token,
then emits the exact FS IPC v1 request bytes used by the owned-copy transport.

Legacy `io_rw` callers still pass raw buffer addresses. Those calls are
deliberately rejected with `registered-buffer-required` (`-95`) rather than
inventing a `SosixBufferRef`. A null pointer is rejected separately as
`invalid-raw-buffer` (`-14`). Serial I/O does not use this filesystem boundary
and retains its compatibility behavior.

## Scenarios

- A registered read preserves operation generation and request-token
  correlation in the encoded v1 request.
- Missing reply endpoints fail before encoding.
- Non-null legacy pointers expose the buffer-registration prerequisite.
- Null legacy pointers retain a distinct invalid-address diagnostic.

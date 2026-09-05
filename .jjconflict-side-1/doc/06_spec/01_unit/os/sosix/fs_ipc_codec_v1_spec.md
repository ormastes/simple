# SOSIX Filesystem IPC v1 Wire Codec

This executable unit contract freezes a pure-Simple, packed little-endian wire
format for asynchronous filesystem requests and completions. The codec does
not invoke syscalls, send IPC, expose pointers, or grant capabilities.

## Frozen layouts

The request is exactly 88 bytes:

- 48-byte header: ABI major, header size, API ID, flags, operation slot and
  generation, reply endpoint, request token, deadline, and a zeroed reserved
  word.
- 40-byte descriptor: capability slot/generation, resource offset, transfer
  length, buffer slot/generation, and buffer offset.

The completion contains a 48-byte header followed by exactly `payload_length`
bytes. Its header carries ABI major, header size, API ID, flags, correlated
operation slot/generation and request token, signed status, payload length,
transferred byte count, and a zeroed reserved word. Payloads are capped at
4096 bytes.

## Fail-closed evidence

The executable spec checks:

- exact sizes and representative byte offsets in little-endian order;
- read-at and write-at API matching;
- ABI/header mismatch, short/long input, and nonzero reserved bytes;
- unknown flag bits;
- resource and registered-buffer offset/length overflow;
- completion API, operation-generation, and request-token correlation;
- exact completion payload length, including missing and trailing bytes;
- negative status, transferred count, and payload round-trip.

Source: `test/01_unit/os/sosix/fs_ipc_codec_v1_spec.spl`

Implementation: `src/os/sosix/fs/ipc_codec_v1.spl`

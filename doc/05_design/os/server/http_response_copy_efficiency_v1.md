# SimpleOS HTTP Response Copy Efficiency V1

## Scope

The filesystem-launched `servers_user` HTTP/1 owner preserves the existing
routes, security headers, connection-close framing, 64 KiB complete-wire cap,
and socket retry limit. The implementation remains Pure Simple.

## Ownership and wire contract

- Text responses retain the canonical `HttpResponse` serializer.
- Static files remain `[u8]` from filesystem read through socket send. Only the
  canonical HTTP head is encoded from text; file bytes are neither decoded nor
  re-encoded.
- `Content-Length` is the exact external byte-body length.
- Admission checks `head length + body length <= 65,536` with subtraction after
  first proving the head fits, avoiding integer overflow/underflow. No response
  bytes are sent when the complete wire response does not fit.
- The head is sent before the body, and the body is attempted only after the
  complete head succeeds. Connection close remains the failure boundary.

## Performance contract

The previous retry loop allocated and copied `remaining` on every partial
write, making adversarial one-byte progress quadratic in response size. The
range sender now stages at most 4 KiB from the checked offset and passes that
packed byte array through the existing validated socket adapter. Raw payload
pointers and array-object header arithmetic are forbidden because array element
layout differs between runtimes. Full-progress copy work is O(response bytes);
each send attempt copies at most 4 KiB. After a positive partial write, the
window shrinks to the observed progress; it doubles only after a complete
window write. This bounds oscillating short-write copy amplification while
allowing full-progress sends to return quickly to 4 KiB chunks. The existing
error/zero-progress budget adds at most 64 bounded chunk copies. No
response-sized suffix is allocated on a retry.

Static-file assembly previously copied the file bytes into text and then copied
the complete response back into bytes. V1 sends one encoded head plus the
original file byte array, eliminating both full-file transformations and the
combined response allocation. The data layout remains two contiguous buffers,
and dispatch stays at one send loop per buffer.

## Evidence

`test/01_unit/os/apps/servers_user/http_response_copy_contract_spec.spl` covers
canonical external-body framing, negative length rejection, offset-borrowing,
the complete-wire cap shape, and absence of both former copy patterns. Per user
instruction, this change was statically reviewed only; the spec was not run.

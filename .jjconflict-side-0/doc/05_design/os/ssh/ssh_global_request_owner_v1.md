# SSH Global Request Owner v1

## Problem

The authenticated SimpleOS SSH session previously ignored every RFC 4254
global request. An OpenSSH `keepalive@openssh.com` request with `want-reply`
therefore received no response, while unsupported requests did not receive the
required `SSH_MSG_REQUEST_FAILURE` response.

## Ownership and bounds

`SshSession` remains the sole mutable connection owner and performs dispatch.
`ssh_global_request_classify` observes an immutable packet value, retains
nothing, and returns one scalar decision. The enclosing SSH packet bounds the
u32-sized request name; checked subtraction reserves the `want-reply` byte
before offset addition. Classification is O(1), performs no substring, text,
or name-sized allocation, and response material is exactly zero or one byte.

## Policy

- malformed framing closes the connection fail-closed;
- requests with `want-reply = false` produce no response;
- every well-framed unsupported request with `want-reply`, including OpenSSH's
  intentionally unsupported `keepalive@openssh.com`, produces
  `REQUEST_FAILURE`; either success or failure is a valid keepalive response.

This deliberately does not implement TCP forwarding or
`no-more-sessions@openssh.com`; those require additional authoritative
connection state and policy owners.

## Static acceptance surface

The unit specification covers keepalive failure-as-liveness-response,
unknown-request failure, response suppression, opaque request-specific tails,
truncation, empty names, and complete names longer than 256 bytes. Runtime
verification was explicitly not run.

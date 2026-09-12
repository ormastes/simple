# SimpleOS filesystem WebSocket integration status
**Status:** OPEN (unverified 2026-09-12)

`/SERVERS.ELF` now recognizes a bounded RFC 6455 upgrade, transfers coalesced
read-ahead bytes to the connection owner, answers Ping, validates Pong, echoes
Close, and closes from the original HTTP socket scope. Ordinary HTTP behavior
remains on its prior framing/response path.

Plaintext `ws://` at exact `/ws` is reachable through an explicitly audited
development listener bound to all guest interfaces; QEMU hostfwd may narrow
host-side exposure but is not treated as a guest bind guarantee. WSS remains
unavailable because this executable has no TLS transport.
Browser `Origin` requests fail closed until an allowlist exists. Authentication,
subprotocols, extensions, and an application message endpoint remain open work
and must not be inferred from frame support.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

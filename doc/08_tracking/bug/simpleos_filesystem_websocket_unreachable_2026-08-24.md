# SimpleOS filesystem WebSocket remains unreachable

`/SERVERS.ELF` classifies only ordinary HTTP routes and closes every accepted
HTTP socket after one response. It does not recognize or retain an RFC 6455
upgrade. The bounded pure-Simple handshake/frame owner now exists as an
unwired prerequisite, but this record stays open until the HTTP connection
owner transfers validated upgrade authority, socket ownership, and read-ahead
tail bytes without bypassing TLS/auth/origin/admission policy.

No WebSocket or WSS availability may be claimed from the prerequisite alone.

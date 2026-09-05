# SimpleOS HTTP/1 Host Authority V1

## Scope

The filesystem-launched `/SERVERS.ELF` plaintext development listener validates
every supplied `Host` field before routing. This is an HTTP authority-syntax
prerequisite only; it does not claim HTTPS, TLS, WSS, certificate identity, or
configured virtual-host binding.

## Deployment profile

Accepted authorities are bounded ASCII DNS/IPv4-style reg-names, optionally
followed by a nonzero port up to 65535, or bracketed IPv6 literals with an
optional valid port. DNS labels are 1 through 63 characters, contain only ASCII
letters, digits, and interior hyphens, and the reg-name is at most 253 bytes.

The deliberately narrow SimpleOS profile rejects userinfo, path, query,
fragment, Unicode, percent escapes, empty labels, invalid hyphen placement,
unbracketed IPv6, zero/overflowing ports, and oversized authority values.

## Ownership and cost

`Http1RequestFrameOwner` validates the already-trimmed field value once when its
line completes. The scanner is O(n) in the authority length, uses constant
state, allocates no split/lowercase collections, and remains invariant to socket
fragmentation. Canonical shared `body_decision` retains sole ownership of
duplicate singleton-header policy and its existing error semantics.

Unit coverage records accepted DNS, port, and IPv6 forms plus representative
authority-confusion failures. Runtime verification is deferred by explicit user
instruction.

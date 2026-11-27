# Dashboard authentication source review

Independent source review, 2026-10-25. **Compilation and runtime execution:
NOT_RUN.** No verified Phase 3 producer was available for this review. This is
not a native security or release qualification.

## Findings

No concrete P0/P1/P2 finding remains in the reviewed `web_login.spl` candidate
after the author replaced raw token storage with SHA256 digests and replaced
lossy URL decoding with strict byte decoding.

**Closed in source: P2 adjacent caller exposure.** Both server entrypoints now
bind `127.0.0.1`. The login validator applies the shared loopback Host/Origin
boundary before routing, and the main server applies it to login, logout and
mux API routes. This closes the earlier non-loopback credential submission
finding in the reviewed source; actual socket binding remains NOT_RUN.

**Residual availability limitation:** both accept loops process a connection
serially. Their 15000 ms socket timeout applies to each read; the shared TCP
`read_line_bounded` owner reads one byte per call. A peer that sends bytes before
each timeout can occupy the server substantially longer than 15 seconds. The
byte/header caps bound storage and eventual byte count, not total request time.
An absolute request deadline and a slow-sender TCP regression are still needed
before claiming bounded request latency. No authentication bypass follows from
this observation; source review does not qualify live availability.

Overall source-review status is **WARN**, not production verification PASS.

## Reviewed behavior

- Configuration is absolute-path, bounded to4096 bytes, read by the existing
  regular/no-follow byte owner, decoded through the text IO owner, and parsed
  with SDN duplicate-key issues rejected. Missing/malformed configuration
  revokes existing leases. Credential fields and configured limits are checked.
- PBKDF2 parameters remain600000..1000000 iterations with32-byte output.
  Password derivation occurs before the username comparison. The source limits
  authentication attempts to8 per60-second monotonic window, including invalid
  forms; native cost and latency are not measured here.
- Registry entries contain only token digest, username and expiry. Raw tokens
  are returned to the caller, not retained in the lease registry. Lookup and
  logout hash supplied bearer tokens; presenting the stored digest itself does
  not authorize or revoke the original token. Randomness is checked through the
  existing entropy owner; provider qualification is not inferred from source.
- Forms reject duplicate credential fields and unknown fields. Percent octets
  are parsed strictly and canonical UTF8 validation rejects malformed bytes
  while preserving a legitimate U+FFFD password character. Session cookies
  require the exact name; duplicates and folded headers fail closed. `local`
  and arbitrary 64-character tokens do not create a session.
- Expiry, logout, configuration rotation and session capacity are checked on
  the actual registry. The cookie is HttpOnly and SameSite=Strict; server-side
  expiry remains authoritative. Secure transport and origin admission belong
  to the caller, not to this cookie helper.
- The authored lifecycle uses eight admitted attempts and six derivations;
  positive logins remain explicit rather than treating a refusal as success.
  Its valid-U+FFFD positive and malformed `%FF` negative distinguish strict
  validation from replacement decoding. Digest-as-cookie/logout negatives are
  meaningful. Early Result returns flow back through environment restoration
  and owned-file cleanup before assertions. The scenario requires a fresh,
  serial process and a private fixture root.
- The shared HTTP boundary tracks whether Host and Origin occurred separately
  from their values. Duplicate or folded headers fail even on reads; duplicate
  Origin cannot be mistaken for absent optional Origin. Mutations require the
  exact `http://` origin matching the admitted loopback authority. Logout also
  requires that origin or a same-authority Referer with a slash delimiter.
- Both auth callers check `session != nil` or `candidate != nil` before binding
  a concrete `DashboardAuthSession` from the payload. No static/local cookie
  value enters the mux authorization branch. This is the intended source
  control flow; native optional-payload lowering remains an execution gate.
- Request/header lines are limited to8192 bytes and128 header lines. Aggregate
  header and body limits are32768/8192 bytes in the validator and65536/65536
  bytes in the main server; appended separator bytes can make the accumulated
  header buffer exceed its nominal cap by one byte, still bounded. Duplicate
  Content-Length, unsupported Transfer-Encoding, negative/oversize body lengths
  and failed reads close the connection. The TCP `read_bytes` owner reads exactly
  the requested bytes and performs strict UTF8 admission. Response Content-Length
  uses UTF8 bytes. These limits do not imply an absolute request deadline.
- The three new pure boundary scenarios assert exact authority, duplicate/folded
  rejection and missing-versus-invalid Origin behavior. Their mirrored manual
  correctly says NOT_RUN and does not substitute for the separate real product
  TCP/login/mux system scenarios. No new transport or application PASS is claimed.

No shared crypto or `black_box` owner was changed or activated by this candidate.
The comparison loops are best-effort source structure, not a claim about native
optimizer output, constant-time machine code or thread-safety of unrelated
runtime helpers. Live restart, entropy-fault, transport-origin, concurrent-owner
and process evidence remain separate unexecuted obligations.

## Input pins

| File | SHA256 |
|---|---|
| src/app/llm_dashboard/web_login.spl | 85b63161624ee15c51fda1121a0cb9af8d28cd0132f04284f6a23e1e6b7cd9b2 |
| test/03_system/app/llm_dashboard/feature/web_login_auth_spec.spl | a3ccf4498dbe614a1d7fe7d2b5152bf05ead024336d430d1bf62e5bcda2ab42e |
| doc/06_spec/03_system/app/llm_dashboard/feature/web_login_auth_spec.md | 3433a72c1030edb3bee7a43adef31d9d4f05545987dc6110de19e959be7ed283 |
| src/app/llm_dashboard/login_only_server.spl | a3a557e4c7134a0727065a815003b34f1bc24dfd4e34981b30e50c648f4ab924 |
| src/app/llm_dashboard/http_auth_boundary.spl | 77c52cd27711868a2b64c24ba696b6acc46b887eea2d7d8635fc58982bcb0502 |
| src/app/web_dashboard/server.spl | 1a8b830ab1a9a4fb47887c5ad8f0da38b94c045330de924f7ebb2b1e44ca31c3 |
| test/01_unit/app/llm_dashboard/http_auth_boundary_spec.spl | 67436863ea11fd15f9249938f44aed0b8711d3392b8d931e36b058bd9fb41157 |
| doc/06_spec/01_unit/app/llm_dashboard/http_auth_boundary_spec.md | 99e69cac5025dbbdd8c630a4eaaad19196223933503753e24208a30d4b6b4dd2 |

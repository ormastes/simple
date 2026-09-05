# TLS facade cannot upgrade an existing fd — STARTTLS (SMTP 587 / IMAP 143) is unimplementable

- Date: 2026-08-25
- Area: runtime / src/lib/nogc_sync_mut/io/tls_sffi.spl / app llm_caret mail
- Status: OPEN (runtime lane)

## Symptom
`mail_send` with `[mail] smtp_port: 587` (and any IMAP-with-STARTTLS setup on
143) must refuse: after the plaintext `STARTTLS` handshake succeeds, the live
TCP socket has to be wrapped in a TLS client session IN PLACE, and no runtime
entry point can do that. The client-side negotiation itself is fully
implemented and spec-proven (src/app/llm_caret/infra_mail_starttls.spl,
test/01_unit/app/llm_caret/infra_mail_starttls_spec.spl); only the socket
upgrade is missing.

## Evidence that no backing extern exists
- `src/runtime/runtime.h` rt_tls_* surface (lines 388–396): connect-by-host /
  connect-by-address only; every entry creates its OWN socket.
- `src/runtime/runtime_https_openssl_core.c:363`: `SSL_set_fd(connection->ssl,
  connection->fd)` is already used internally by `rt_tls_client_connect` —
  the OpenSSL mechanism exists, it is just not reachable for a caller-owned fd.
- `src/compiler_rust/runtime/src/value/net_tls.rs`: no from-fd/upgrade entry.
- Declaring the extern anyway is forbidden: an unbacked extern silently
  returns nil (.claude/rules/vcs.md, unbacked-extern ratchet).

## Needed runtime symbol (C-side design, ~10 lines)
```c
/* Wrap an ALREADY-CONNECTED socket in a TLS client session.
 * Takes ownership of fd on success (rt_tls_client_close closes it);
 * on failure the fd is left open and owned by the caller.
 * server_name: SNI/verification hostname (rt string handle).
 * Returns a TLS handle (>0) or <=0 on handshake failure. */
int64_t rt_tls_client_from_fd(int64_t fd, int64_t server_name) {
    SimpleTlsConnection *c = simple_tls_connection_alloc();
    if (!c) return 0;
    c->fd = (int)fd;                      /* skip the connect() path */
    if (!simple_tls_handshake(c, rt_text_cstr(server_name)))  /* SSL_new +
        SSL_set_fd(c->ssl, c->fd) + SSL_connect, as rt_tls_client_connect
        already does from line 363 */
        { simple_tls_connection_free_no_close(c); return 0; }
    return simple_tls_register(c);
}
```
Rust seed: mirror in net_tls.rs (rustls `ClientConnection` over a
`TcpStream::from_raw_fd`) + interpreter_extern registration, or an honest
error until implemented — never a silent nil.

## Facade to add once backed
`tls_upgrade_fd(fd: i64, host: text) -> TlsClientConnection` in
tls_sffi.spl; then wire `app.llm_caret.infra_mail_starttls.starttls_begin/feed`
into infra_mail after `STARTTLS`→`220` (SMTP) / tagged `OK` (IMAP), and add a
third live row to scripts/check/check-llm-caret-infra-live.shs.

## Refusal today
infra_mail refuses before connecting:
"mail_send: smtp_port 587 needs STARTTLS: mail: port 587 needs STARTTLS, and
the runtime has no in-place TLS upgrade (missing rt_tls_client_from_fd; ...)".

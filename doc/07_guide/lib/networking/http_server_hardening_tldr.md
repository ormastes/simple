# HTTP Server Hardening — TL;DR

One policy, two transports: `std.common.net.http_core` owns request limits,
Content-Length/chunked policy, bounded chunked decoding, path safety, and
route pattern matching for BOTH `nogc_sync_mut` and `nogc_async_mut`
http_server. Async enforces limits DURING parsing (before buffer growth).

```sdn
diagram: {
  client -> edge_proxy: "TLS / HTTP2 (external)"
  edge_proxy -> transport: "private HTTP/1.1"
  transport: {sync_http_server, async_http_server}
  transport -> http_core: "limits + body_decision + path_is_safe + decode_chunked_bounded"
  async_http_server -> handler_registry: "dynamic handler_type, under task security context"
  async_http_server -> inline_static: "static only, path re-checked before root+path"
}
```

Violations: 431 line/header limits, 400 invalid/duplicate CL + CL-with-chunked
smuggling ambiguity + unsafe path, 413 declared/decoded body too large,
501 chunked on sync (fail closed) or unregistered handler type.

Evidence: `http_core_spec` (23), sync `parser_limits`/`path_safety`/
`chunked_rejection` (66), async `async_parser_limits` (18),
`async_path_safety` (8), `async_dynamic_dispatch` (6).

Full guide: `http_server_hardening.md`. Lane:
`.spipe/simple_enterprise_suite/state.md`.

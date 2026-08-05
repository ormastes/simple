# Network stack works; its "e2e" coverage is an illusion, and the spec tree is duplicated 5,591x

**Status:** OPEN (findings; nothing deleted)
**Found:** 2026-08-05
**Component:** `test/02_integration/app/ui.web/`, `src/lib/nogc_async_mut/net/`,
`test/unit` vs `test/01_unit`
**Attribution:** all runs on the **Rust bootstrap seed** (`bin/simple` prints the
seed warning banner), not the self-hosted binary.

## The good news, proven against a non-Simple client

Simple's TCP stack really moves bytes. A server started with `bin/simple run` on
127.0.0.1 was driven by a **bash `/dev/tcp` client** — no Simple on the client
side at all, so the in-process shim hypothesis is excluded:

```
ss -ltnp: LISTEN 127.0.0.1:39872  users:(("simple",pid=3674839,fd=4))
HTTP/1.1 200 OK / Content-Length: 28 / PONG-FROM-SIMPLE-SERVER-4242
SERVER_GOT_REQUEST_LINE GET /external HTTP/1.1
```

Simple-to-Simple also verified with matching peer ports (`CLIENT_LOCAL
127.0.0.1:54908` / `SERVER_PEER 127.0.0.1:54908`), so the kernel genuinely
brokered the connection.

Socket chain: `src/lib/nogc_sync_mut/io/tcp.spl:43` (`TcpListener.bind` ->
`rt_io_tcp_bind`, extern at `:491`) -> `runtime/src/value/net_tcp.rs:390`
`native_tcp_bind` -> `std::net::TcpListener::bind` (`net_tcp.rs:121`). The
interpreter path lands at `interpreter_native_net.rs:505/507`.

**The wire is plaintext HTTP/1.1.** No TLS on this path. TLS exists and is
rustls-backed (`runtime/src/value/net_tls.rs`, `rt_tls_client_connect`) but was
not exercised — it needs certificates.

## Defect 1: the "e2e" spec never opens a socket

`test/02_integration/app/ui.web/ws_e2e_spec.spl` reports
`Results: 46 total, 43 passed, 3 failed` and looks like network coverage. It is
**not**. Measured on the file:

- `rt_file_read_text` / `to_contain` occurrences: **142**
- socket calls (`tcp_`, `connect`, `bind`, `listen`): **0**

Every example reads a source file as text and asserts a substring is present.
The 3 failures are **grep-string drift** — handler/parser source moved past the
literals — not protocol failures. So 46 examples that read as websocket
end-to-end coverage would stay green through any change that keeps the source
text intact, and go red on a pure rename that breaks nothing.

**Only 3 spec files in the entire `test/` tree bind a socket:**
`01_unit/lib/nogc_async_mut/io/async_tcp_spec.spl` (measured
`Results: 14 total, 14 passed, 0 failed`), `host_io/net_async_spec.spl`, and
`simpleos_riscv_network_gate_spec.spl`.

## Defect 2: a dead extern API that fails silently

`src/lib/nogc_async_mut/net/sffi.spl:17-38` declares `tcp_listener_bind`,
`tcp_stream_connect` and siblings. **None is registered anywhere in
`src/compiler_rust/`:**

    grep -c '"tcp_listener_bind"'  common/src/runtime_symbols.rs  -> 0
    grep -c '"tcp_stream_connect"' common/src/runtime_symbols.rs  -> 0
    grep -c '"rt_io_tcp_bind"'     common/src/runtime_symbols.rs  -> 1   (the live API)

Per the documented defect, an unregistered `@extern` returns **nil silently**
under the JIT. So any caller routed through `net/sffi.spl` fails without an
error. Either register these or delete the declarations — leaving them is a trap.

## Defect 3: the spec tree is duplicated

`test/unit` and `test/integration` are stale mirrors of `test/01_unit` and
`test/02_integration`:

| pair | same relative path in BOTH | old-only | new-only |
|---|---|---|---|
| `test/unit` vs `test/01_unit` | **5,005** | 3 | 1,971 |
| `test/integration` vs `test/02_integration` | **586** | 0 | 123 |

**5,591 spec files exist at the same relative path in two trees.** Of 40 sampled
shared unit specs, **39 are byte-identical**; the divergent ones are worse than
the identical ones, because the two copies silently disagree. `ws_e2e_spec.spl`
is one such: 373 vs 375 lines, different md5.

Consequences: a fix applied to one tree leaves the other stale; any repo-wide
spec count is inflated by ~5.6k; and a reader cannot tell which copy the runner
executes.

**Nothing was deleted here.** Removing a duplicate tree reroutes callers rather
than deduplicating them, and which tree is authoritative is a decision for the
owner. Establish that first, then delete in one sweep with the runner's path
resolution confirmed.

## Reproduce

```
grep -cE 'rt_file_read_text|to_contain' test/02_integration/app/ui.web/ws_e2e_spec.spl   # 142
grep -cE 'tcp_|connect|bind|listen'     test/02_integration/app/ui.web/ws_e2e_spec.spl   # 0
comm -12 <(cd test/unit && find . -name '*_spec.spl'|sort) \
         <(cd test/01_unit && find . -name '*_spec.spl'|sort) | wc -l                    # 5005
```

# SSH: client proven real, daemon cannot bind on host, and six duplication sites

**Status:** OPEN (findings; nothing edited or deleted)
**Found:** 2026-08-05
**Attribution:** all runs on the **Rust bootstrap seed** (`bin/simple` prints the
seed banner), box at load 51 on 32 cores.

## Client: proven to drive a real socket

Not a shim. The Simple SSH client connected to a non-Simple peer (python3
listener on 127.0.0.1:22023) and sent **390 bytes** of real protocol:

```
ss -ltnp -> LISTEN 127.0.0.1:22023 python3 pid=3674572   peer accepted 127.0.0.1:53034
client -> "SSH-2.0-SimpleOS_1.0\r\n" then 00 00 01 6c 07 14 ...
          (len 0x16c, msg 0x14 = SSH_MSG_KEXINIT, containing "curve25519-sha25...")
client <- "ssh: server version: SSH-2.0-ProbePeer_1.0"
```

It then failed correctly at `parse server KEXINIT frame` because the stub peer
sent none. Live client is `src/os/tools/net/ssh_tool.spl` -> `_SshTool/{run,transport}.spl`
(1,045 lines, entry `run_ssh(args)`).

## Daemon: hard-blocked on host — its network layer is baremetal-only

```
[sshd] Ed25519 live helper self-test: PASS
[sshd] Host keys ready
error: semantic: unknown extern function: rt_boot_tcp_bind
```

All **8** `rt_boot_tcp_*` externs the daemon uses (`bind`, `accept_timeout`,
`write_text`, `send_kexinit_fixed`, `send_kex_reply_{fixed,ed25519}`,
`send_newkeys_fixed`, `send_plain_payload`) have **0 definitions** in
`src/runtime/runtime_native.c` — independently confirmed. The only definition
site is `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c:3277`.

So `src/os/apps/sshd/` (27 files, 8,943 lines) cannot serve on a host OS at all.
Its designed gate is a QEMU SimpleOS boot
(`test/03_system/os/ssh_live_login_in_qemu_spec.spl`), and no `build/os/`
artifacts exist here. **This is not "the daemon works like the web server"** —
the web server binds a real host socket via `rt_io_tcp_bind`; the SSH daemon
cannot.

## Specs: unmeasurable here, no verdict obtained

Zero `Results:` lines. Every log stops at 93,083 bytes of lint/gc warnings —
the runner never reaches execution.

| spec | outcome |
|---|---|
| `ssh_client_host_key_spec.spl` (`--timeout 600`, outer 900s) | rc=143, NO verdict line |
| same, default timeout | rc=255, `Process timed out` (120s child cap) |
| `sshd/ssh_mac_spec.spl` | 600s -> rc=143, NO verdict line |

Not a pass, not a fail — **unmeasurable on this box at this load.**

## Crypto: genuine, unlike the TLS format library

`ssh_kex_core.spl:36-70` calls real `x25519_base`/`x25519` (`os.crypto.curve25519`)
and `sha256`, building the RFC 4253 exchange hash and key derivation over live
bytes. Negotiation is real (`ssh_session_kex.spl:549,729-733`). Only 6 `_hex`
helpers exist and all are debug formatters — contrast `src/lib/*/tls/`, which is
formatting-only.

Advertised: kex `curve25519-sha256`; host key `ssh-ed25519,rsa-sha2-256,rsa-sha2-512`;
cipher `aes256-gcm@openssh.com,aes128-gcm@openssh.com,aes256-ctr`; MAC
`hmac-sha2-{512,256}-etm`.

**No post-quantum KEX in SSH.** No `mlkem`/`sntrup`/`kyber` anywhere in the SSH
tree. Unlike TLS's orphaned `0x11EC` constant, nothing is dangling here — there
is simply no PQ group, so SSH is further from PQ than TLS, not closer.

## Duplication — six sites

1. **Two parallel crypto trees.** `src/os/crypto/` (118 files) vs
   `src/lib/common/crypto/` (28), with **14 overlapping names**: sha256,
   ed25519, aes_gcm, chacha20{,_poly1305}, poly1305, blake2s, blake3, argon2,
   pbkdf2, pem, ecdsa_p256, sha512, x25519_mlkem768. Sampled 7 — **none is a
   re-export**; they are genuine second implementations (ed25519 637 vs 1,526
   lines). SSH imports only `os.crypto.*`, while 15 `os/crypto` files reach into
   `common.crypto`. This is the largest duplication in the tree.
2. **Two AES-GCM packet layers.** `ssh_cipher.spl` (502 L) and
   `ssh_cipher_live.spl` (285 L) both define `ssh_encrypt_packet_aes_gcm`,
   `ssh_decrypt_packet_aes_gcm`, `_make_nonce`, `_push_byte`, `_u8_at` — **5
   colliding names**. The server session uses `_live`; the client and `mod.spl`
   use the other.
3. **Two client stacks.** `_SshTool` (1,045 L, live) vs
   `src/os/apps/ssh_client/` (1,566 L, "socket-free by construction", **zero
   production importers** — only 4 test files).
4. **A near-duplicate file.** `src/app/io/ssh_ffi.spl` vs
   `src/lib/nogc_sync_mut/io/ssh_sffi.spl`, 384 lines each, differing in one
   comment word (`FFI` -> `SFFI`). Hashes `b50b8c2b` vs `37824d33` — near-identical,
   NOT byte-identical. `app.io.ssh_ffi` has **zero importers**.
5. **A dead third stack.** `ssh_sffi.spl` declares **30 externs**
   (`rt_ssh_*`/`rt_sftp_*`); **none** is defined in `src/runtime/`. Unregistered
   externs return nil silently under the JIT. `ssh_terminal.spl` (242 L) wraps it
   and has 5 importers.

   **Sub-finding addressed, 2026-08-06 (narrow scope only — see below).**
   Re-verified independently: `grep -rn "rt_ssh_\|rt_sftp_" src/runtime/` is
   empty, and none of the 30 names resolve anywhere in `src/compiler_rust/`
   (source, not just build output) either — confirmed dead, not just
   under-grepped. File is
   `src/lib/nogc_sync_mut/io/ssh_sffi.spl` (the tier files under
   `nogc_async_mut`/`gc_sync_mut`/`gc_async_mut` are thin re-exports, as noted
   above). `ssh_terminal.spl`'s 5 real importers: `terminal/connection.spl`,
   `terminal/power/host_power.spl`, `terminal/credential/config_parser.spl`,
   `terminal/__init__.spl`, and `nogc_async_mut/terminal/credential/__init__.spl`
   (the 3 tier `ssh_terminal.spl` re-export files don't count as separate
   importers). These are reachable from real production code, not just tests:
   `src/app/test_daemon/adapters/remote_pc_adapter.spl` (a real app under
   `src/app/test_daemon/`, which has its own `main.spl`/`daemon.spl`) reaches
   `ssh_terminal.spl` transitively via `std.terminal.connection`.

   Fix (does NOT implement any SSH/SFTP functionality — scope stays "make the
   failure loud", per the recommended-order item 2 above): `ssh_sffi.spl`'s
   extern block is now documented UNBACKED (same convention as
   `nogc_async_mut/net/sffi.spl`'s UDP/HTTP block from
   `network_coverage_illusion_and_spec_tree_duplication_2026-08-05.md`), and
   `ssh_terminal.spl` — the sole real call-site layer, confirmed by grep that
   nothing outside it and the tier re-exports imports `ssh_sffi` directly — now
   calls an unconditional (never level-gated, always-on) `stderr_write`
   diagnostic at the top of all 6 public functions
   (`ssh_terminal_connect/execute/send/receive/upload/download/close`) stating
   plainly that the SFFI backing has zero `src/runtime/` definitions and the
   call always fails, with a pointer back to this doc. `std.log.log_error` was
   considered and rejected: it is gated by `SIMPLE_LOG` and silent by default,
   which would have reproduced the exact silent-failure hazard this is fixing.

   Verified with a standalone probe calling `ssh_terminal_connect` against
   `bin/simple run` (Rust bootstrap seed) in both default and
   `SIMPLE_EXECUTION_MODE=jit`: before this change the call returned
   `connected=false` with no diagnostic distinguishing "not implemented" from a
   real connection failure; after, stderr now prints
   `ssh_terminal: ssh_terminal_connect(host=127.0.0.1, port=22023) -- ssh_sffi
   backing (rt_ssh_*/rt_sftp_*) has zero definitions in src/runtime/; this call
   always fails. See doc/08_tracking/bug/
   ssh_daemon_baremetal_only_and_duplication_2026-08-05.md#5-a-dead-third-stack`
   before the (unchanged) `connected=false` return. On this seed the interpreter
   path also separately logs its own `rt_interp_call error: ... unknown extern
   function: rt_ssh_connect` — i.e. this specific engine was not fully silent
   either — but the new `.spl`-level diagnostic is unconditional and does not
   depend on that engine-specific behavior, so it holds under the documented
   silent-JIT case too. `bin/simple lint` on both changed files: 0 errors (3
   pre-existing, unrelated `unnamed_duplicate_typed_args` warnings in
   `ssh_sffi.spl` untouched by this change).

   No existing spec covers `ssh_terminal.spl` (`find test -iname
   "*ssh_terminal*"` is empty), so nothing broke and there was no
   silent-nil-shaped spec to flag.

   Explicitly NOT done here (out of scope for this sub-finding): no
   `rt_ssh_*`/`rt_sftp_*` runtime primitives were implemented, findings #1-4 and
   #6 are untouched, and `src/app/io/ssh_ffi.spl`-vs-`ssh_sffi.spl` (finding #4)
   was not touched.
6. **Legacy spec trees.** SSH-affecting: 7 legacy unit + 5 legacy system files,
   all content-divergent from their live twins. See
   `doc/08_tracking/dedupe/`.

Correctly structured, for contrast: the tier files
`src/lib/{nogc_async_mut,gc_sync_mut,gc_async_mut}/io/ssh_*` are thin
`export use` re-exports of the single `nogc_sync_mut` implementation. That is
the pattern the crypto trees should follow and do not.

## Recommended order

1. Decide whether the SSH daemon is meant to serve on a host OS. If yes, it needs
   host `rt_boot_tcp_*` implementations (or a port to `rt_io_tcp_*`, which
   already works). If no, say so — "SSH daemon" currently implies more than it
   delivers.
2. Delete or register the 30 dead `rt_ssh_*`/`rt_sftp_*` externs; a silently
   nil-returning API is worse than a missing one.
3. Retire whichever of the two client stacks and the two AES-GCM layers is not
   load-bearing — after confirming which, not before.
4. The two crypto trees are a design decision, not a cleanup. Do not merge them
   without an owner ruling.

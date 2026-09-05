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

## Follow-up investigation, 2026-08-06 (findings 1-4 — no deletions, no merges)

Scope: one level deeper on findings 1-4 (finding 5 was already fixed
2026-08-06 by a sibling agent, commit `90a4048e4ce2afdf94d02636611e3d649abd4ecf`,
untouched here; finding 6 untouched). Nothing was deleted or merged in this
pass — see per-finding verdicts below for why.

### Finding 1 (crypto trees) — full 14-name table, no exceptions found

Sampled all 14 overlapping names fresh (not just the 7 the original doc left
unsampled). All 13 simple-file pairs have real `fn` bodies on **both** sides
(no re-export found anywhere) — the pattern generalizes with zero exceptions.
`x25519_mlkem768` is structurally different from the other 13 and should not
be read as the same kind of duplication: `src/os/crypto/x25519_mlkem768/`
(8 files, GPU/CUDA/Vulkan/Metal NTT acceleration — `cuda_ntt_provider.spl`,
`vulkan_ntt_provider.spl`, `metal_ntt_provider.spl`, `accelerator_cache.spl`)
and `src/lib/common/crypto/x25519_mlkem768/` (8 files, evidence/attestation —
`performance_attestation.spl`, `qualified_timing.spl`, `matrix_receipt.spl`)
address different concerns (hardware KEM acceleration vs. measurement
receipts), not the same primitive implemented twice.

| name | os/crypto lines | common/crypto lines | os prod importers | os test importers | common prod importers | common test importers |
|---|---|---|---|---|---|---|
| sha256 | 403 | 414 | 10 | 28 | 58 | 23 |
| ed25519 | 637 | 1,526 | 12 | 35 | 0 | 0 |
| aes_gcm | 639 | 718 | 1 | 6 | 2 | 0 |
| chacha20 | 738 | 206 | 1 | 9 | 0 | 0 |
| chacha20_poly1305 | 229 | 282 | 3 | 21 | 0 | 0 |
| poly1305 | 283 | 283 | 0 | 9 | 0 | 0 |
| blake2s | 402 | 209 | 0 | 3 | 0 | 0 |
| blake3 | 579 | 853 | 0 | 2 | 0 | 0 |
| argon2 | 622 | 581 | 0 | 3 | 0 | 0 |
| pbkdf2 | 127 | 252 | 0 | 2 | 1 | 0 |
| pem | 278 | 203 | 0 | 3 | 0 | 0 |
| ecdsa_p256 | 332 | 73 | 4 | 9 | 0 | 3 |
| sha512 | 626 | 1,558 | 1 | 7 | 1 | 0 |
| x25519_mlkem768 | (dir, 8 files, GPU/NTT) | (dir, 8 files, attestation) | 8 | 31 | 0 | 0 |

(Counts are `grep -rl 'use os.crypto.<name>.'` / `use (std.)?common.crypto.<name>.'`
hits outside each tree's own directory; production excludes `test/`.)

Reading: **`os.crypto` is the tree SSH actually depends on** — every SSH
production import goes through `os.crypto.*` (matches the original doc's
"SSH imports only `os.crypto.*`" line, now confirmed name-by-name). `sha256`
is the one name where `common.crypto` has dramatically more usage (58 prod
importers vs. 10) — that's because `common.crypto.sha256` is the
general-purpose stdlib hash used all over the tree outside SSH, not a
SSH-specific competitor. For the other 12 named pairs, `common.crypto` has
0-2 production importers each — largely unused outside its own tree and a
handful of tests. Net: this is not "two trees each half-used" — it's one
actively-depended-on tree per name, and for 12 of 13 non-sha256 names that
tree is `os.crypto`. Still a genuine architecture decision (real duplicate
logic, not dead weight on either side) — no merge performed.

Aside, out of assigned scope, flagged for whoever owns this: there is
actually a **third** crypto surface, `std.crypto` (`src/lib/crypto.spl` +
`src/lib/crypto/{sha256,sha512,sha1,hmac,hkdf,pbkdf2,legacy_hash,types}.spl`),
used e.g. by `src/app/package.registry/{signing,verify}.spl`. Not
investigated further here — noted only so the eventual crypto-tree ruling
accounts for it instead of rediscovering it later.

### Finding 2 (AES-GCM packet layers) — confirmed genuine split, not accidental duplication

Split still exists exactly as described. Fresh importer check:

- `ssh_cipher.spl` (502 L, pure Simple — imports `os.crypto.{aes_gcm,
  chacha20, chacha20_poly1305}`, zero `extern fn`): imported by
  `src/os/apps/sshd/mod.spl`, **and by the live client**
  `src/os/tools/net/_SshTool/{run,transport}.spl`, plus
  `test/03_system/os/os_ssh_spec.spl` (+ its `test/system/` legacy twin) and
  two integration specs.
- `ssh_cipher_live.spl` (285 L, header literally says "live-safe AES-256-GCM
  only" — declares 5 `extern fn`s: `rt_tls13_aes256_gcm_encrypt/decrypt`,
  `rt_ssh_aes256_gcm_decrypt_packet[_payload_len]`, `rt_bytes_u8_at`):
  imported only by `src/os/apps/sshd/ssh_session.spl` (the server's live
  session loop) and its own unit spec plus
  `rv64_ssh_live_login_in_qemu_spec.spl`.

This reads as a **deliberate split, not accidental duplication**: `ssh_cipher.spl`
is the portable pure-Simple reference implementation used by the client and
by generic/system tests; `ssh_cipher_live.spl` is a C-accelerated variant
built specifically for the server's baremetal/QEMU-booted live session path
(consistent with `.spipe/ssh_native_survey/state.md`'s independent note that
"the shipped server's bulk-crypto hot path is C-accelerated, not pure
Simple"). The 5 colliding names never collide at compile time — no file
imports both modules together. **Recommendation, not performed:** don't
blind-merge. If consolidation is wanted, the real options are (a) port the
C-accelerated primitives behind the portable `os.crypto.aes_gcm` API with a
target/build-flag switch so both callers share one module, or (b) keep the
split but rename `ssh_cipher_live.spl` to something that says *why* it exists
(e.g. `ssh_cipher_baremetal.spl`) so the next reader doesn't read it as
accidental drift the way this bug doc's title implied.

### Finding 3 (two client stacks) — REVERSED from "safe to delete": confirmed active WIP, do not delete

Fresh grep, both narrow (`src/app src/os`, excluding self and `test/`) and
repo-wide including `test/`:

```
grep -rln 'ssh_client' src/app src/os --include=*.spl | grep -v test
  -> only files inside src/os/apps/ssh_client/ itself
grep -rn 'os\.apps\.ssh_client\|apps/ssh_client' src/ test/ --include=*.spl \
  | grep -v '^src/os/apps/ssh_client/'
  -> only the 4 test files: ssh_client_host_key_spec.spl,
     ssh_client_protocol_spec.spl, ssh_client_kex_inprocess_spec.spl,
     ssh_client_session_flow_spec.spl
```

The one apparent hit outside the dir, `src/os/apps/sshd/ssh_session.spl:53`
(`fn _live_openssh_client_version_bytes()`), is a false positive — a function
name, not an import. **"Zero production importers" is confirmed, still true
today.**

However: **do not delete this.** `.spipe/ssh_native_client/state.md` (lane
SSHCLI, dated 2026-07-27, "slice shipped, spec-proven, not yet wired to a
socket") documents `src/os/apps/ssh_client/` as a deliberate, in-progress
replacement client architecture, not dead/duplicate code. It reuses the
sshd protocol core directly (packet/transport/KEX modules imported from
`os.apps.sshd`, not reimplemented) and adds exactly the pieces the live
`_SshTool` client is missing: `ssh_known_hosts.spl` (host-key **pinning** —
independently confirmed here, `grep -c known_hosts src/os/tools/net/_SshTool/*.spl`
is 0, i.e. `_SshTool` really has none) plus a socket-free state machine meant
to be testable without a live server. The lane's own doc says explicitly:
"this lane is complementary, not duplicative — but it does mean there are now
two client trees, and that must be resolved (next increment #1)." Zero
production importers here is the *expected* state of a lane still mid-flight
on its own documented next increment (wiring to a socket), not a signal of
abandonment. Deleting it would discard real security-relevant work (MITM
protection `_SshTool` lacks) with no replacement. **Recommendation:** leave
both stacks; the real next step is finishing the SSHCLI lane's own
"increment #1" (decide whether `_SshTool` adopts the new socket-free core or
is retired in its favor) — that is an implementation decision for the lane
owner, not a duplication cleanup.

### Finding 4 (near-duplicate `ssh_ffi.spl`/`ssh_sffi.spl`) — already resolved, no action needed

`src/app/io/ssh_ffi.spl` **does not exist** in the current tree or at `HEAD`
(`920136b593979eab310126d5e4de6a97b27e9888`). `find src -iname 'ssh_ffi.spl'`
and a repo-wide `grep -rln '\bssh_ffi\b'` (excluding `ssh_sffi`) both return
nothing — no file, no lingering references, and the stale
`scripts/check/ui_backend_isolation_baseline.txt` entry the original doc
flagged is already gone too. History shows this was done in commit
`7ba93b8c0b1` ("refactor(ssh): delete the duplicate ssh_ffi module and its
dangling tier facades") — that commit is not an ancestor of current `HEAD`
(likely a parallel/rewritten jj lineage), but its effect is already present
in the current tree, so there is nothing left to delete here. Verified this
does not touch `ssh_sffi.spl`/`ssh_terminal.spl` (finding 5, already fixed
and out of scope) — neither was modified in this pass. **Finding 4: resolved,
no further action.**

### Net status

- Finding 1: still OPEN, owner decision needed. Comparison table above ready
  to act on.
- Finding 2: still OPEN, owner decision needed. Recommendation above ready to
  act on; leaning "genuine split with a naming problem," not "accidental
  duplication."
- Finding 3: reclassified from "candidate for deletion" to **do not delete —
  active WIP**; resolve via the SSHCLI lane's own next increment, not via
  this bug.
- Finding 4: **resolved** (already deleted elsewhere in history; confirmed
  clean in current tree). No further action.
- Overall doc status stays **OPEN** — findings 1-2 (and 3, now reframed) are
  unresolved design decisions; only finding 4 (and finding 5, previously) are
  closed.

## Re-verification, 2026-08-10 (no changes — architectural findings confirmed unchanged)

Spot-checked the two claims the whole doc's daemon-vs-client conclusion rests
on, fresh:

- `timeout 20 /usr/bin/grep -rn "rt_boot_tcp_bind" src/runtime/runtime_native.c`
  -> still **0 hits**; the same symbol is still defined 5 times in
  `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`. The daemon's
  host-bind blocker is unchanged.
- `timeout 20 /usr/bin/grep -rln "rt_ssh_\|rt_sftp_" src/runtime/` -> still
  empty. Finding 5's fix (loud-failure diagnostic in `ssh_terminal.spl`,
  commit `90a4048e4ce2afdf94d02636611e3d649abd4ecf`) remains the correct scope
  — no runtime primitives exist to back a real implementation.

Findings 1 (two crypto trees), 2 (two AES-GCM layers), 3 (two client stacks,
now "active WIP, do not delete"), and 6 (legacy spec trees, owned by
`doc/08_tracking/dedupe/`) are genuine architecture-ownership decisions, not
bugs with a code-level fix available in this pass — repeating the 2026-08-06
investigation would not change that. **No code changed in this re-verification
pass.** Status stays OPEN / architectural, pending an owner ruling on findings
1-2 and completion of the SSHCLI lane's own next increment for finding 3.

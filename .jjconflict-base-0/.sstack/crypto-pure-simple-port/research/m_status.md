# SSH+TLS Crypto Port — Reconciled Status (R-A, 2026-04-25)

Sources: `doc/08_tracking/todo/compiler_bugs_for_crypto_2026-04-25.md`,
`doc/08_tracking/todo/ssh_tls_modern_algorithms_2026-04-25.md`,
`doc/09_report/crypto_spec_remains_2026-04-16.md`, HEAD `git log -50`,
`git worktree list`, working-tree diff in `src/os/apps/sshd/*` and
`src/lib/common/runtime_symbols.spl`.

## TL;DR
- **Closed:** B1, B2, B3, B5, B6 — five of the seven blockers gone in 24 h.
- **Open compiler work:** B4 (`bits[lo..hi]` sugar) and B7 hunt-list (no real repros yet).
- **Unblocked milestones:** M1 (SSH advert) and M2 (ETM + cert host keys) have zero compiler dependencies remaining.
- **Highest-leverage non-compiler next step:** ship M1 §1.1–§1.5 — reorder cipher list, add Terrapin strict-kex, finish ECDSA host-key blob.
- **Highest-leverage *compiler* next step:** B4 bitfield sugar — pays back across every AES/SHA/GCM round.

## Compiler bugs (B1–B7)

| ID | Title | Status | Gating commit / location | Owner / worktree |
|----|-------|--------|--------------------------|------------------|
| B1 | Release wrapper drops error detail | **CLOSED** | `35b4a54e92 fix(cli): route _cli_eprint through real stderr (closes B1)` | landed on main |
| B2 | Interpreter `[u8]` quadratic on multi-MiB | **CLOSED** | `e4b572b7c4 feat(interp): add rt_bytes_alloc extern (closes B2)` | also present in worktrees `a27da0bd5f…`, `a31415db59…`, `a9fac9ea5e…` |
| B3 | SSpec `--mode=smf` wrapper class hoisting | **CLOSED** | `50027aef07 docs(crypto-bugs): mark B3 verified-fixed` (fix landed 2026-04-17 in `preprocess_sspec_for_smf`) | residuals R1 (`class` inside `it`) and R2 (`skip()` keyword) tracked but not blocking |
| B4 | `bits[lo..hi]` get/set sugar + `u32::byte/with_byte` | **OPEN** | parser + HIR work, `lib/common/crypto/aes/round.spl` rewrite | unassigned; no worktree currently on this |
| B5 | `match` int → jump-table codegen | **CLOSED** | `379a08503d feat(mir,codegen): jump-table lowering for dense int match (closes B5)` | landed on main |
| B6 | CT-compare branch-fold guard (`rt_black_box`) | **CLOSED** | `d42cde3a0f feat(crypto): add rt_black_box opaque-identity intrinsic (closes B6)` | landed on main |
| B7 | Hunt-list H-1..H-8 (speculative) | **OPEN, none triggered yet** | open per-repro during §1–§6 | candidate **H-9** spotted (see Risks) — not yet filed |

## Algorithm milestones (M1–M5)

| ID | Title | Status | B-deps | Next concrete step |
|----|-------|--------|--------|--------------------|
| M1 | SSH advert — modern OpenSSH 9 defaults (§1) | **READY (unblocked)** | B1 ✓ | reorder `CIPHER_ALGORITHM` in `ssh_transport.spl` (§1.1/1.2); add `kex-strict-s-v00@openssh.com` + Terrapin reset (§1.3); finish `_build_host_key_blob_for_algo` ECDSA blob (§1.4); add `ssh_extinfo.spl` + `SSH_MSG_EXT_INFO` (§1.5) |
| M2 | ETM MACs + cert host keys (§2 + §4.2) | **READY** | B1 ✓ | implement `hmac-sha2-{256,512}-etm@openssh.com` MAC ordering; add OpenSSH cert host-key parsing |
| M3 | TLS 1.3 end-to-end (§5.1 + §5.2) | **READY (compiler-side)** | B1 ✓ B3 ✓ B5 ✓ B6 ✓ | start §5.1 primitives — SHA-3/Keccak-f[1600] (`common/crypto/sha3.spl`), HKDF-Expand-Label (`tls/key_schedule.spl`), Ed25519 verify, RSA-PSS, ECDSA P-256/P-384 verify; needs sustained primitive work before any handshake code |
| M4 | HTTPS web UI on `https://`+`wss://` (§6.1–§6.4) | **GATED on M3** | inherits M3 | not actionable until §5.2 lands |
| M5 | PQ KEX on SSH+TLS (§3 + §5.4) | **GATED on M3** | B1 ✓ B2 ✓ B3 ✓ B6 ✓ | depends on §5.1.1 SHA-3 first; ML-KEM-768 NTT over Z/3329 needs CT compare (B6 ✓) and bulk byte alloc (B2 ✓) |
| M6 | HTTP/2 over ALPN h2 (§6.5) | **GATED** | inherits M4 | tracked, not scheduled |

## Cross-cutting math/infra gaps (identification only)
- **Bignum / `[u64]`:** RSA-PSS sign+verify (§5.1.4) and ML-KEM NTT (§3.1) need a non-quadratic big-int representation. Hunt-list **H-5** (`[u64].push` quadratic) will likely fire here. No `Vec::with_capacity` analogue exists today.
- **GF(2¹²⁸) for GCM:** GHASH currently absent; no `clmul` intrinsic — H-4 candidate.
- **Curve25519 26-bit-limb field math:** depends on `u64.mul_hi` codegen quality — H-3 candidate; not yet measured.
- **Constant-time discipline:** B6 lands `rt_black_box`; ML-KEM rejection sampling and Curve25519 cswap will be the first real consumers.
- **CSPRNG:** §1 fallback uses C-side random (per memory). No pure-Simple CSPRNG identified for §3 PQ keygen. Sourcing strategy is R-B/R-C scope.
- **AES T-tables:** const init pathway not validated — H-2 candidate.
- **Bitfield sugar (B4):** absence multiplies AES/SHA/GCM line count ~10× per the doc.

## Recommended next 5 work items (priority order)
1. **M1 §1.1–§1.5 (SSH modern advert + Terrapin + ECDSA blob + EXT_INFO).** All B-deps closed, files already touched in WC, ships TODAY without compiler work. This is the cheapest user-visible win.
2. **B4 bitfield sugar.** Highest-leverage compiler item; gates clean AES T-tables, SHA round, and GCM polynomial mul. Slow turn — start in parallel with #1.
3. **M3 §5.1.1 SHA-3 / Keccak-f[1600] + SHAKE.** Hard prerequisite for both M3 (HKDF) and M5 (ML-KEM). Pure Simple, no exotic compiler features needed.
4. **File the unreported H-9 baremetal-text bug** (see Risks #1) so future agents don't re-introduce the byte-literal workaround.
5. **M3 §5.1.2–§5.1.5 (HKDF-Expand-Label, Ed25519 verify, RSA-PSS, ECDSA P-256/P-384 verify).** Once §5.1.1 lands, these unblock all of TLS 1.3 handshake.

## Risks
1. **WC has an unreported baremetal text-encoding bug.** `ssh_build_auth_failure` in `src/os/apps/sshd/ssh_auth.spl` now hard-codes `[0x70,0x75,0x62,…]` for `"publickey,password,keyboard-interactive"` instead of letting `ssh_put_text` encode it. This is a real H-class bug (candidate **H-9**: baremetal `ssh_put_text` mis-encodes ASCII punctuation), not stylistic. Must be filed in `doc/08_tracking/bug/` and the workaround removed once fixed.
2. **WC has an AES-GCM packet-framing correctness fix.** `ssh_encrypt_packet_aes_gcm` in `src/os/apps/sshd/ssh_cipher.spl` was rewritten so the encrypted body is block-aligned with the cleartext `packet_length` as AAD (RFC-correct for `aes*-gcm@openssh.com`). **Any agent landing M1 §1.1/§1.2 must preserve this rewrite** — do not regenerate the function from origin/main.
3. **WC also swaps `os.kernel.log.klog_api` → `os.userlib.log` in `ssh_kex.spl`/`ssh_session.spl`** and adds `extern fn rt_net_recv_ssh_encrypted_packet`. Ensure these stay paired with the cipher-framing change; partial commits will break the userland sshd build.
4. **Worktree double-counting.** `agent-a05aa744` and `agent-a5532aa6` show statuses via `../../../` — they share main's working tree, not independent. The "11 worktrees" framing overstates parallelism; effectively ~3 distinct heads (`d42cde3a0f`, `f708bc21d2`, `c047d3dbff`) plus skill-init worktrees (`a1b455fd`, `a5af98c4`, etc.) with no crypto work. **No worktree is currently on B4 or any M-milestone.**
5. **Bootstrap-rebuild discipline.** B2/B6 added `rt_bytes_alloc` and `rt_black_box` externs; `runtime_symbols.spl` is updated in WC but not yet committed. Per memory `feedback_extern_bootstrap_rebuild.md`, any new `rt_*` work in §5/§6 must run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`, NOT `bin/simple build`.
6. **R1/R2 SSpec residuals.** `class` inside `it{}` and `skip("…")` still fail compiled-mode; crypto KAT loaders that use either pattern must avoid them or stay in interpret mode until R1/R2 are fixed.
7. **Pre-existing crypto failures (`crypto_spec_remains_2026-04-16.md`).** Issue #1 (`poly1305_finalize` wrong tag byte[0]) and Issue #2 (interpreter wraps FFI sign returns in `Option<[u8]>`) are still listed as open in that report. Re-verify status before shipping M1 — both predate the recent B-fixes and may now reproduce differently.

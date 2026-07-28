# TODO P1/P2 Triage — 2026-07-27

Read-only triage of the "528 open items: P1=7, P2=21" backlog claimed by
`doc/TODO.md`. **Headline finding: `doc/TODO.md` is stale and its P1/P2 counts
are both wrong and inflated by a symlink-duplication bug in the TODO scanner.**
Details below, then per-item triage, then recommendations.

## 0. Generator disagreement (doc/TODO.md vs todo_db.sdn)

| | `doc/TODO.md` | `doc/08_tracking/todo/todo_db.sdn` |
|---|---|---|
| mtime | 2026-07-07 05:05 | **2026-07-27 22:02** (today, current) |
| Open P1 | 7 | **52** rows / **46 unique** items |
| Open P2 | 21 | **28** rows / **10 unique** items |
| Open P3 | 500 | 500 (matches) |

`doc/TODO.md` is 20 days stale relative to the database it's generated from.
Its own P1=7/P2=21 figures are *self-consistent* with its stale snapshot, but
that snapshot itself double(-triple-, quadruple-...)-counts: `src/std` is a
symlink to `src/lib` (`ls -la src/std` → `src/std -> lib`), and
`test/01_unit/compiler`, `test/unit/compiler`, `test/unit/lib/database/lib`,
`test/feature/lib/lib` etc. are symlink trees back to `src/compiler` /
`src/app`. The TODO scanner walks through these symlinks (unlike
`_driver_collect_sources`, which uses `find` without `-L` per
`doc/09_report/stage4_campaign_summary_2026-07-27.md` §2), so **one physical
TODO comment is reported once per symlinked path it's reachable from** —
confirmed by `md5sum` identity across all 7 reported paths for both the P1 and
P2 texts (all `7575e8cc0b4d82f02ef5dd9e10d0d2ef` for the P1 signature file).

Net effect: `doc/TODO.md`'s "7 P1 items" is **1 unique issue x 7 mirror
paths**, and its "21 P2 items" is **3 unique issues x 7 mirror paths**. This
is the *same architectural bug* (symlink-duplicate reporting) already
identified independently in the stage-4 HIR error count
(`stage4_campaign_summary_2026-07-27.md` §2, "~28% of the count is duplicate
reporting") — it is a generic defect in how tools here enumerate `src/`, not
specific to the TODO scanner.

Separately, `todo_db.sdn` (regenerated today) carries **46 unique open P1**
and **10 unique open P2** items that `doc/TODO.md` never mentions at all —
mostly narrative backlog entries (macOS/Windows/FreeBSD bootstrap dynload,
SimpleOS host-GPU, RISC-V, and the fresh 2026-07-27 compiler/HIR fixes, ids
119, 529–594). These were **not** part of the "7+21" the triage was scoped
to and were not individually code-verified in this pass — see §4 for a
compact appendix and a follow-up recommendation.

## 1. Per-item triage — the "7 P1 + 21 P2" set (doc/TODO.md)

All 7 P1 rows share one text; all 21 P2 rows are 3 texts x 7 paths. Table
below lists each **unique** item once, with all its mirror `file:line`
locations, per the task's request to quote verbatim and resolve file:line.

| # | Pri | Verbatim text | file:line (canonical `src/lib` copy; 6 more mirrors at identical content, see §0) | Classification | Effort | Blocker |
|---|---|---|---|---|---|---|
| P1-A (ids 6,40,96,155,355,418,487) | P1 | "Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with 'method len not found on type enum (receiver value: Option::Some(...))'. ... Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md." | `src/lib/nogc_sync_mut/io/signature_sffi.spl:129` | **DONE-ALREADY** | n/a | none |
| P2-A (ids 19,53,109,168,368,431,500) | P2 | "Interpreter loses the `self` binding when a struct" | `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:1304` | **STALE/UNCLEAR** | n/a | none identified |
| P2-B (ids 20,54,110,169,369,432,501) | P2 | "wire transport-level send queue" (full context: "`# TODO: [quic-server][P2] wire transport-level send queue`") | `src/lib/nogc_async_mut/io/quic/quic_server.spl:288` | **ACTIONABLE-NOW** | Small | none |
| P2-C (ids 28,62,118,177,377,440,509) | P2 | "extract ALPN from handshake state when ALPN is implemented" (full: "`# TODO: [stdlib][P2] extract ALPN from handshake state when ALPN is implemented`") | `src/lib/nogc_async_mut/http_server/worker.spl:348` | **ACTIONABLE-NOW** | Medium | none |

### P1-A — SFFI `[u8]` Option::Some wrapping — DONE-ALREADY

`grep -n "TODO" src/lib/nogc_sync_mut/io/signature_sffi.spl` returns **zero
hits** — the comment is gone. `git log --oneline -- src/lib/nogc_sync_mut/io/signature_sffi.spl`
shows commit `f9b34943859` ("cleanup(crypto-sffi): remove dead _unwrap_sig
workaround + stale P1 TODO", 2026-07-08 03:27:36 +0000, one day after
`doc/TODO.md`'s last generation): *"The SFFI [u8]->Option::Some wrapping bug
is fixed: os_crypto_ref_signature_spec passes 39/0 with _unwrap_sig made a
passthrough, proving the coercion is no longer load-bearing."* The repro test
file `test/03_system/os_crypto_ref_signature_spec.spl` named in the TODO text
**no longer exists** (`ls` confirms). Current `signature_sffi.spl:129` is
`fn rsa_sha256_sign(pkcs8: [u8], message: [u8]) -> [u8]:` with no
`_unwrap_sig` helper anywhere in the file — matches the commit's described
inlining. **Evidence is unambiguous: this item is fixed and stale in all 7
tracker copies.**

### P2-A — Interpreter loses `self` binding — STALE/UNCLEAR

`grep -n "TODO" src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl` (2292
lines) returns **zero hits** anywhere in the file — not just at line 1304.
Current line 1304 (`metal_host_free(host)`, inside
`_commit_gpu_only_cpu_composite`) has no relation to struct `self`-binding
semantics. `git log --oneline -n10` for this file shows three very recent
Metal-glass commits (`fa6bab7921e`, `801cafb85c1`, `57620a6826d`, all "wm
glass"/"metal" fixes) that could plausibly have touched or removed the
comment during refactoring — a `git log -S"self binding" --all` search timed
out (>2 min) on this repo's full history and was not completed. **Cannot
confirm DONE vs simply removed-without-fixing without a deeper interpreter
self-binding repro; flag as stale tracker data, not a ready-to-pick task.**
Next session: grep repo-wide for any current interpreter self/struct-closure
bug (see `feedback_interp_struct_name_collision_global_registry.md`,
`project_interp_env_get_name_collision_drawir_fix_2026-07-26.md` in project
memory — related but distinct class of interpreter name-resolution bug) before
assuming this is resolved.

### P2-B — QUIC transport-level send queue — ACTIONABLE-NOW (small)

Confirmed live at `quic_server.spl:282-289`:
```
me _flush_outbound():
    """Send any outbound packets queued in the transport layer.
    Currently QuicTransport.on_udp_data processes SendPacket actions
    internally. This method is a hook for future batched sends.
    """
    # TODO: [quic-server][P2] wire transport-level send queue
    pass
```
`_flush_outbound()` is called once per `poll()` (`quic_server.spl:186`) but is
a no-op — the docstring itself says sends already happen synchronously inside
`QuicTransport.on_udp_data`, so **this stub is currently harmless**; nothing
is broken, it's a batching/perf hook that was never filled in. File is 289
lines total. Implementing it means adding an explicit outbound queue to
`QuicTransport`/`quic_server.spl` and draining it here instead of (or in
addition to) the inline send in `on_udp_data` — self-contained, no Dict-heavy
code on this path, no stage-4 dependency (runs fine under the current seed
test lane). **Effort: small** (a few hours) but **value is modest** — it's an
optimization, not a correctness fix; could equally be closed as "not needed
yet" if nobody has hit a throughput problem.

### P2-C — Extract ALPN from TLS handshake state — ACTIONABLE-NOW (medium)

Confirmed live at `worker.spl:348-349`, inside `me handle_tls_accept(...)`
right after a successful `perform_server_handshake`:
```
                # TODO: [stdlib][P2] extract ALPN from handshake state when ALPN is implemented
                self.dispatch_by_alpn("", client_fd, now)
```
i.e. ALPN is hardcoded to `""` (→ HTTP/1.1 always), even though
**the ALPN extension parser already exists and is dead code**:
`src/lib/nogc_async_mut/io/tls_handshake.spl:418`
`fn parse_alpn_extension(ext_data: [i64]) -> text:` (RFC 7301) has **zero
callers anywhere in `src/lib/`** (`grep -rn "parse_alpn_extension" src/lib/`
returns only its own definition). `TlsHandshakeState` (the `state` returned
by `perform_server_handshake`, `tls_handshake.spl:70`) has no `alpn` field —
only `session_keys`, `cipher_suite`, `client_seq`, `server_seq` are read at
`worker.spl:332-346`. Implementing this is a **3-part, well-scoped change**:
(1) call `parse_alpn_extension` on the ClientHello's extension bytes inside
`perform_server_handshake` in `tls_handshake.spl`, (2) add an `alpn: text`
field to the `TlsHandshakeState` struct and thread it through the `Ok(state)`
construction (~line 308-311), (3) read `state.alpn` instead of the literal
`""` at `worker.spl:349`. No Dict-struct interaction, no stage-4 dependency.
**Effort: medium** (touches 2 files, needs an HTTP/2-ALPN round-trip test,
but the hard crypto/parsing part is already written and just needs wiring).

## 2. Blocker check against today's known defects

- **Stage-4 self-hosted bootstrap**: still FAILS per
  `doc/09_report/stage4_campaign_summary_2026-07-27.md` §1 (`bin/simple` is
  still the 2026-07-25 Rust seed; no Linux green stage-4 deploy has ever
  existed in this repo's history). **None of the 4 triaged items require
  stage-4 to be green** — they are ordinary `.spl` library edits, testable
  via the seed-backed `bin/simple test` lane that's in daily use regardless
  of stage-4 status.
- **`Dict.len()` always -1`** (`doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`,
  severity High, OPEN) and **`Dict<K,Struct>.get()` corrupt payload**
  (`doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`,
  severity High, OPEN, native-build only — `.get()` on a hit; `d[k]`,
  `Some(d[k])`, `keys()`, `contains_key()` are unaffected): **neither P2-B nor
  P2-C touches a `Dict<K,Struct>.get()` call on their edited path** — P2-C
  reads/writes plain struct fields and does bracket-assign
  (`self.tls_sessions[client_fd] = TlsSessionState(...)`, `worker.spl:342`),
  not `.get()`. **Not blocked.**

## 3. Top-3 recommendations (ranked by value/effort)

1. **Fix the TODO-scanner's symlink duplication and regenerate `doc/TODO.md`.**
   Highest leverage, smallest fix: the scanner over-reports by ~7x on any
   file reachable through `src/std`, `test/*/compiler`, `test/*/app`, etc.,
   producing exactly the false "P1=7" backlog this triage had to unwind by
   hand. Sketch: make the TODO-scan's directory walk skip symlinked
   subtrees (mirror `_driver_collect_sources`'s `find` without `-L`
   behavior, or canonicalize-and-dedupe by realpath before recording a row),
   then rerun `bin/simple todo-scan` to refresh both `todo_db.sdn` (already
   current) and `doc/TODO.md` (20 days stale) from the same, now-correct,
   pass. This single fix collapses the reported P1 count from 52 rows/46
   unique to an accurate number and prevents every future session from
   re-discovering the same false "7 items" framing.
2. **Wire ALPN extraction into the TLS handshake (P2-C, `worker.spl:348` +
   `tls_handshake.spl:418`).** Real, scoped, medium-effort work with the hard
   part (RFC 7301 parsing) already written and idle. Sketch: add an
   `alpn: text` field to `TlsHandshakeState`; inside
   `perform_server_handshake`, after parsing ClientHello extensions, call the
   existing `parse_alpn_extension(ext_data)` and store the result on the
   state; change `worker.spl:349` from the literal `""` to `state.alpn`; add
   an HTTP/2-via-ALPN system spec exercising `dispatch_by_alpn` with a
   non-empty negotiated protocol (today only the `""` → HTTP/1.1 path is
   exercised, since nothing ever produces a different value).
3. **Implement or explicitly close the QUIC outbound send-queue hook (P2-B,
   `quic_server.spl:282-289`).** Small effort either way. Sketch: if pursuing
   it, add a `Vec<SendPacket>`-style queue field to `QuicTransport`, have
   `on_udp_data` push instead of send-inline, and have `_flush_outbound`
   drain it with basic coalescing; if not pursuing it now, replace the bare
   `pass` with a one-line `# not needed: on_udp_data already sends inline;
   revisit if profiling shows send-path contention` so the tracker stops
   flagging a harmless stub as open backlog.

*(P2-A, the `self`-binding item, is intentionally excluded from the top-3 —
it's STALE/UNCLEAR, not actionable, until someone spends investigation time
confirming whether the underlying interpreter issue still exists anywhere.)*

## 4. Appendix — live `todo_db.sdn` P1/P2 backlog not covered by doc/TODO.md

For the next session: `todo_db.sdn` (current as of today) has **46 unique
open P1** and **10 unique open P2** items beyond the 4 above. None were
individually code-verified in this pass (out of scope — this triage was
bounded to the "7+21" `doc/TODO.md` explicitly named). They cluster in:
bootstrap/dynload cross-platform verification (ids 530-533, mostly "run a
verification pass" not "write code"), SimpleOS host-GPU/QEMU (119, 529, 537,
544, 548-552, 563-569, 575, 577-578, 586), and a batch of **fresh
2026-07-27 compiler/HIR fixes** already tied to today's stage-4 campaign
(557-562, 579-585, 589-594 — several of these overlap 1:1 with items already
narrated in `stage4_campaign_summary_2026-07-27.md` §3, e.g. id 592 = the
HIR module-namespace call-lowering fix, id 559 = the `rfind` Optional
regression). **Recommended follow-up**: triage ids 557-594 next — they are
the freshest, most concretely-described, and most likely to be small/medium
actionable work, several with existing partial fixes and named repair steps
already in the stage-4 report (§5.3 "first task for next session", §6.1-6.6).

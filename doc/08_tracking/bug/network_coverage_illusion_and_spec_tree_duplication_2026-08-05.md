# Network stack works; its "e2e" coverage is an illusion, and the spec tree is duplicated 5,591x

**Status:** OPEN (findings; nothing deleted)

**Re-confirmed 2026-08-09:** re-read in full. This doc is a measurement/
characterization record, not a single localized code defect — its content is
findings about which specs give real network coverage vs. illusory
substring-on-source-text coverage, plus a spec-tree duplication count. No
further code change is prescribed by the doc itself beyond "nothing deleted"
pending a decision on which illusory specs to rewrite or remove. Confirmed
accurate on re-read; no new contradicting evidence found. Left OPEN as
characterized — the remedy (rewriting/deleting illusory specs, deduplicating
the spec tree) is a scoped follow-up project, not a same-session point fix.
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

> **CORRECTION 2026-08-05 — one of the "3 real socket specs" is itself vacuous.**
>
> The sentence below counts `01_unit/lib/nogc_async_mut/io/async_tcp_spec.spl`
> as one of only three specs in the tree that bind a socket, and cites its
> `14 total, 14 passed, 0 failed` as a measured result. **It opens no socket and
> asserts nothing.** All 14 of its example bodies are the literal `0`, with the
> socket code left commented out. Evidence, on the file:
>
> ```
> $ grep -vcE '^\s*#|^\s*$'  test/01_unit/lib/nogc_async_mut/io/async_tcp_spec.spl   # 42  non-comment lines
> $ grep -cE  '^\s+0\s*$'    test/01_unit/lib/nogc_async_mut/io/async_tcp_spec.spl   # 14  bodies that are just `0`
> $ grep -cE  '^\s*(val|var|expect|await)' test/01_unit/lib/nogc_async_mut/io/async_tcp_spec.spl  # 0
> $ grep -c   '^use '        test/01_unit/lib/nogc_async_mut/io/async_tcp_spec.spl   # 0  — it does not even import a TCP type
> ```
>
> A representative example, verbatim:
>
> ```simple
> it "documents async bind":
>     # val listener = await AsyncTcpListener.bind("0.0.0.0:8080")?
>     # expect listener.is_open() == true
>     0
> ```
>
> So its 14 green examples are the *same* illusion Defect 1 describes, one layer
> deeper: not "asserts on source text" but "asserts nothing at all". The
> corrected count is **2** specs that bind a socket, not 3
> (`host_io/net_async_spec.spl` and `simpleos_riscv_network_gate_spec.spl`);
> `01_unit/lib/net_server/net_server_spec.spl` is a third that does real
> loopback TCP with byte-exact oracles and was missed by the original sweep.
>
> A replacement with real assertions now exists at
> `test/01_unit/lib/nogc_async_mut/net/net_tcp_facade_spec.spl`
> (`Results: 4 total, 4 passed, 0 failed`), proven non-vacuous by sabotage:
> flipping one expected payload byte yields
> `Results: 4 total, 3 passed, 1 failed` with
> `expected [80, 79, 78, 71, 33] to equal [80, 79, 78, 71, 34]` — the reported
> bytes are the real bytes that crossed the kernel socket.

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

### Update 2026-08-05 — scope was wider than "lines 17-38", and it is now fixed

Re-derived per-symbol: **all 41** externs in the file were unbacked, not just the
24 TCP ones. Four names produce grep hits and **none is a registration** —
`tcp_stream_connect` / `udp_socket_connect` are entries in `security.rs`'s
ambient-API *policy* table, `http_request` is in `effects.rs` `NET_OPERATIONS`,
and `bytes_to_string` is an *interpreter-only* dispatch entry (absent from
`runtime_symbols.rs`, so still silent-nil under JIT/native).

Reach was also wider: `std.net.*` resolves to the **`nogc_async_mut` tier first
from every tier** (`module_loader_resolve.spl`: "Default app mode is
nogc_async_mut"), so this one file backed all four tiers' `net/` modules.

Resolution: TCP callers were rerouted onto the registered `rt_io_tcp_*` family
(`net/tcp.spl` is now a facade over `std.nogc_sync_mut.io.tcp`) and the 24 dead
TCP externs deleted; `bytes_to_string` / `file_write_bytes` were reimplemented in
pure Simple over `rt_bytes_to_text` / `rt_file_write_bytes`; the 14 `udp_socket_*`
plus `http_request` and the three `url_*` remain declared but are now marked
UNBACKED with TODOs, because live importers exist and **no** runtime symbol
exists to reroute them to (the registry contains zero `udp`-bearing symbols).

### Do NOT attribute this JIT failure to that fix

`bin/simple run` cannot drive the live TCP classes at all. This predates the
reroute. Exact reproduction — run both, they fail byte-identically:

```
# via the new facade
SIMPLE_TIMEOUT_SECONDS=0 bin/simple run test/04_smoke/net_tcp_facade_jit_probe.spl

# CONTROL: same file, single import line changed to bypass the facade and hit
# the live implementation directly:
#     use std.nogc_sync_mut.io.tcp.{TcpListener, TcpStream}
SIMPLE_TIMEOUT_SECONDS=0 bin/simple run /tmp/control_direct.spl
```

Both print:

```
Runtime error: Function 'nil.local_addr' not found
Runtime error: unresolved symbol -- this is a code-generation dispatch gap, not a program error.
```

i.e. `TcpListener.bind(...)` matched `Ok(l)` but bound `l` to **nil** under the
JIT. Because the control bypasses the facade entirely and fails the same way,
the defect is in the JIT's `Result` binding, not in `std.net.tcp`. The
interpreter path is green (4/4). Note `SIMPLE_TIMEOUT_SECONDS=0` is required —
otherwise `kill_simple_monitor` kills the run at 60s CPU with exit 143 and no
verdict line.

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

### Update 2026-08-06 — authority established; discovery-guard extended, full deletion NOT yet performed

Re-verified with a fresh directory diff (all files, not just `*_spec.spl`):
`test/unit` (8,306 files) vs `test/01_unit` (15,036 files) — **8,287 shared
paths, 0 files unique to `test/unit`**; `test/integration` (978 files) vs
`test/02_integration` (1,610 files) — **978 shared paths, 0 files unique to
`test/integration`**. The "old-only" counts in the table above (3 and 0) are
now stale in the safe direction: the 3 `test/unit`-only specs cited in
`doc/08_tracking/bug/test_unit_legacy_mirror_divergence_2026-08-04.md` were
already migrated forward (commit `fb742496235`, before this task started), so
there is nothing left to triage on that axis for either tree.

**Evidence the numbered trees are authoritative:**
- `src/lib/nogc_sync_mut/test_runner/test_runner_files.spl` is the sole
  discovery implementation (`nogc_async_mut` just re-exports it). It already
  special-cases `test/unit/` as a "FROZEN legacy mirror" excluded from
  directory discovery — a fix landed one day earlier
  (`doc/08_tracking/bug/test_unit_legacy_mirror_divergence_2026-08-04.md`,
  same root cause, same conclusion, independently reached) — but that guard
  had never been extended to `test/integration/`, so `test/integration/`
  specs were still being silently discovered and run alongside
  `test/02_integration/` on every default `bin/simple test` invocation.
- Every comment, cache-skip rule, and cover-annotation check elsewhere in
  `src/app/test_runner_new/` refers only to the numbered tree
  (`test/01_unit/`, `test/02_integration/`, `test/03_system/`); there is no
  code path anywhere that treats `test/unit/`/`test/integration/` as a first
  class discovery root.
- Content check: of 8,287 shared-path files in the unit pair, 884 diverge
  (matches the 874 figure from the 2026-08-04 doc); of 978 shared-path files
  in the integration pair, 91 diverge. Every sampled divergent pair (10
  sampled across both trees, plus the two called out here) shows the numbered
  tree as an equal-or-larger, syntactically newer successor — e.g.
  `test/unit/app/branch_coverage_7_spec.spl` still uses `!= nil` where
  `test/01_unit/.../branch_coverage_7_spec.spl` uses `.?`;
  `test/integration/app/app_mcp_intensive_spec.spl` loops `0..99` and uses
  unquoted dict keys where `test/02_integration/.../app_mcp_intensive_spec.spl`
  loops `0..100`, uses quoted keys, and sets an extra env var. No sample in
  either direction showed the legacy tree ahead.
- Git history on `main` could not be used to date the numbered tree's
  introduction — local history has been rewritten/compacted enough that
  `git log -- test/01_unit` and `git log -- test/unit` both bottom out at
  the same 2026-08-05 commit — so the "numbering convention == later
  reorganization" claim rests on the code/content evidence above, not commit
  archaeology.

**What was done:** extended `is_legacy_mirror_path`/`targets_legacy_mirror` in
`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl` to also exclude
`test/integration/` from directory discovery, mirroring the existing
`test/unit/` guard exactly (excluded from directory scans only; naming a path
under either legacy tree explicitly still runs it). This closes the live half
of Defect 3: `bin/simple test` (or any directory-scoped run) no longer
double-executes/double-counts `test/integration/` against
`test/02_integration/`, matching the behavior already shipped for
`test/unit/` vs `test/01_unit/` a day earlier.

**What was NOT done:** the full deletion of `test/unit/` and
`test/integration/` (9,284 files combined). The evidence above is
unambiguous, and the prior 2026-08-04 investigation reached the identical
conclusion with equally strong evidence — but that session *also* chose the
conservative discovery-guard step over deletion ("a smaller interim step, if
deletion is too aggressive"), and this session found the working copy under
the same conditions that make a ~9k-file deletion risky to land right now:
heavy concurrent multi-agent load (10+ load average, 165 unrelated dirty
files from other sessions in `git status` at task start) and this repo's own
documented history of `main` being wiped to near-zero twice via large/bad
pushes (`.claude/rules/vcs.md` § Pre-push guards). Recommendation for the
owner: once the working copy is quiet, delete `test/unit/` and
`test/integration/` in one sweep (no further triage needed — 0 files are
unique to either tree), gated by
`sh scripts/check/check-tree-size-push.shs --expect-files <post-count>` per
the guard's own instructions.

## Reproduce

```
grep -cE 'rt_file_read_text|to_contain' test/02_integration/app/ui.web/ws_e2e_spec.spl   # 142
grep -cE 'tcp_|connect|bind|listen'     test/02_integration/app/ui.web/ws_e2e_spec.spl   # 0
comm -12 <(cd test/unit && find . -name '*_spec.spl'|sort) \
         <(cd test/01_unit && find . -name '*_spec.spl'|sort) | wc -l                    # 5005
```

---

## Re-verification 2026-08-17 (io lane) — no code defect in `src/lib/nogc_sync_mut/io/tcp.spl`

Re-read against current source. This remains a measurement/characterization
record, not a localized defect, and in particular it does **not** describe a bug
in `tcp.spl`: the doc's own evidence (bash `/dev/tcp` client against a Simple
server, matching peer ports) proves that socket path genuinely moves bytes. The
defect is in the *specs* that claim to cover it — they assert on source-text
substrings — plus the duplicated spec tree.

No change made here. The remedy is a spec-tree project (rewrite or delete the
substring-asserting "e2e" specs, deduplicate `test/unit` vs `test/01_unit`), not
an edit to `src/lib/nogc_sync_mut/io/**`. Left OPEN as characterized.

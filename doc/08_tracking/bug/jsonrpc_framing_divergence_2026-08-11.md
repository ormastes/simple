## 2026-08-17 — the two SPEC-VIOLATING families are fixed; the rest stays a record

The triage note below is right that families D and E are a substrate/typing
refactor to leave alone. It is wrong to file B and C alongside them: those two
are not stylistic divergence, they **disagree with LSP 3.17**, which defines
`Content-Type` as a header field and requires unknown header fields to be
skipped.

- **B** (`src/app/t32_lsp_mcp/protocol.spl`) returned any unrecognised header
  line as a bare JSON-lines message. Real VS Code sends
  `Content-Type: application/vscode-jsonrpc; charset=utf-8`, so B handed that
  header to its JSON parser as a request. The `else:` branch is now a skip.
- **C** (`src/app/lsp_mcp/main.spl`) had no header loop: one `input()`, then two
  blind `input()` calls, declared length discarded. An extra header dropped the
  message; a body containing a newline was truncated. Replaced with the
  canonical loop over a new `stdin_read_char` reader, consuming exactly
  `Content-Length` bytes.

The shared policy those loops must implement is now a specified pure function,
`frame_scan_headers` in `src/app/protocol/framing.spl` (the loops still cannot
literally share code — they differ in their read primitive). Spec:
`test/01_unit/app/protocol/jsonrpc_header_scan_spec.spl`, 7/7; a sabotage that
made an unknown header abort the scan took it to 5/7, revert `diff -q` identical.

**Correction to "All writers" below — that paragraph is FALSE.** Simple's
`text.len()` and `substring` are BYTE-based, not character-based (measured:
`"héllo€".len()` == 9, not 6). Every writer already declares the UTF-8 byte
length the spec requires, and every reader consumes bytes to match. There is no
non-ASCII under-declaration gap. This is now pinned by the last scenario in the
spec above.

**From-source end-to-end proof** (the integration specs cannot see a source
change — they run a prebuilt binary, as the harness note below records). A single
framed `initialize` carrying `Content-Type: application/vscode-jsonrpc;
charset=utf-8` piped into each server:

| Server (run from source) | pre-fix | post-fix |
|---|---|---|
| `src/app/lsp_mcp/main.spl` | **0** framed replies | 1 |
| `.../t32_lsp_mcp/main.spl` | **0** framed replies | 1 |

Both were silently dropping every real VS Code message.

D and E remain out of scope for the reasons already recorded.

## Triage 2026-08-17 — OPEN as designed (record, not a defect to close)

This doc is an accurate enumeration, not a regression: 2 of 11 implementation
sites are merged and sabotage-proven, the other 9 are DIVERGENT with per-site
reasons already recorded. Merging families B/C/D/E is a refactor with real
behavioural risk across LSP/DAP/MCP transports, not a fix this verification pass
should land opportunistically. Left OPEN with its per-site table as the spec for
whoever takes the merge.

# JSON-RPC Content-Length framing: 4 behavioural families, not 20 duplicates

**Date:** 2026-08-11
**Status:** Partially merged. Two sites merged and sabotage-proven; the rest are
DIVERGENT and recorded here with per-site reasons.

## Enumeration (measured, `/usr/bin/grep -rn`, unrestricted)

`/usr/bin/grep -rln "Content-Length"` over the repo excluding `build/` and the
`.claude/worktrees.pre_migrate_backup/` snapshot returns **506 files**. That
number is misleading: the overwhelming majority are HTTP `Content-Length`
response headers (`src/lib/**/http*`, `src/app/ui.web/**`, vendored `ureq`,
`gix-transport`), which are a different protocol concern entirely.

Filtering to files that emit or parse a `Content-Length` header **and** mention
`jsonrpc` gives **37 files**. Removing vendored third-party
(`src/app/vscode_extension/.vscode-test/**` -- 7 bundled Copilot/VS Code
artifacts, `src/compiler_rust/vendor/**`, `src/compiler_rust/lib/**` seed
stdlib) and the mirrored test trees leaves **18 owned live sites**, of which
**11 are implementations** and 7 are test/probe harnesses that construct frames
inline.

The `mcp_common.spl` referenced in the audit is
`src/compiler_rust/lib/std/src/mcp/mcp_common.spl` -- inside the **Rust seed's
vendored stdlib**, not `src/lib/`. It is unreachable from `src/app/**` and is
not a viable merge target.

### Implementation sites

| Site | Family | Merged? |
|---|---|---|
| `src/app/mcp/main.spl:352` `_mcp_read_message` | A (tolerant loop) | **YES** |
| `src/app/simple_lsp_mcp/json_helpers.spl:341` `read_stdin_message` | A (tolerant loop) | **YES** |
| `src/app/t32_lsp_mcp/protocol.spl:40` `lsp_read_stdin_message` | B (strict-else loop) | no |
| `src/app/lsp_mcp/main.spl:175` `read_stdin_message` | C (single-line, no loop) | no |
| `src/app/protocol/transport.spl:16` `read_message` | D (Result-typed, `read_exact`) | no (already canonical for DAP/LSP libs) |
| `src/lib/editor/services/lsp_transport.spl:95` | E (buffer-slice) | no |
| `src/lib/editor/services/debug_session_dap_protocol.spl:46` | E (buffer-slice) | no |
| `src/app/mcp/main_transport.spl:5` (writer only) | writer | no |
| `examples/10_tooling/trace32_tools/cmm_lsp/lsp_server.spl` | B | no |
| `examples/10_tooling/mcpgdb/*.spl`, `src/app/mcpgdb/*.spl` | A-like | no |
| `src/app/svim/lsp_client.spl` | client-side | no |

`src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/{lsp,dap}/transport.spl`
and `src/app/dap/transport.spl` are **already delegating** to
`app.protocol.transport` -- 5 real importers. That hub exists and works
cross-package; it is simply not what the MCP servers use.

## The differences (this is why a blind merge would have changed behaviour)

**Family A** (`mcp/main.spl`, `simple_lsp_mcp/json_helpers.spl`) -- a header
loop that *ignores* unrecognised header lines, so `Content-Type:` and vendor
headers are tolerated. Length parsed by a total `_parse_decimal_raw` that stops
at the first non-digit and never aborts. Returns a per-message JSON-lines flag.
A byte-level diff of the two proved them **identical apart from the `_mcp_`
name prefix**. These are the only two safe to merge.

**Family B** (`t32_lsp_mcp/protocol.spl`) -- looks like A but has an `else:`
branch that treats *any* unrecognised header line as bare JSON-lines input and
returns it immediately. An extra header therefore **breaks** B where it is
harmless in A. It also uses `int(len_str)` (not the total parser) and sets a
**global sticky** `LSP_USE_JSON_LINES` rather than returning a per-message flag.
Merging B into A would silently add extra-header tolerance and change the
JSON-lines latch from global to per-message.

**Family C** (`lsp_mcp/main.spl`) -- **not a loop at all.** It reads one line,
then blindly calls `input()` twice for the blank line and the body, discarding
the declared length entirely. It cannot handle extra headers, cannot handle a
body containing a newline, and cannot handle a split read. This is a latent
defect, not a duplicate; fixing it is a behaviour change that needs its own
spec and its own review.

**Family D** (`app/protocol/transport.spl`) -- a different generation:
`Result`-typed, hard-errors on a missing header and on a non-numeric length,
uses `read_exact(length)`, and has **no JSON-lines fallback**. Strictly less
tolerant than A. Routing the MCP servers into D would break every host that
sends bare JSON lines.

**Family E** (`src/lib/editor/services/*`) -- operates on an in-memory buffer
via `header.slice(i, ...)` rather than on stdin, and is therefore the only
family that is genuinely partial-read aware. Different substrate; not mergeable
without giving A a buffer.

**All writers** declare the length as `body.len()` (characters), not UTF-8
bytes. For the ASCII JSON these servers emit the two coincide, but a non-ASCII
body would under-declare on every one of them. Open gap, unclaimed by the spec.

## What was merged, and the proof it executes

`src/app/protocol/framing.spl` now holds the canonical pure primitives
(`frame_strip_line_end`, `frame_parse_decimal`, `frame_content_length_of`,
`frame_encode`), specified by
`test/01_unit/app/protocol/jsonrpc_framing_spec.spl` (22 scenarios, mirrored
into `test/unit/`). Family A's two sites now delegate.

**Sabotage proof.** With `frame_strip_line_end` altered to return
`"SABOTAGE" + line`, a framed `initialize` request piped into each server *from
source* produced **0** framed replies; with the canonical restored, **1** each:

| Server (run from source) | canonical | sabotaged |
|---|---|---|
| `src/app/simple_lsp_mcp/main.spl` | 1 reply | 0 replies |
| `src/app/mcp/main.spl` | 1 reply | 0 replies |

The unit spec independently went 22/22 -> 14/22 under an arithmetic sabotage of
`frame_parse_decimal`. Revert verified by `diff -q` against the pre-sabotage
copy: zero residue.

## Harness finding: the integration specs are NOT an oracle for source merges

`test/02_integration/app/simple_lsp_mcp_stdio_spec.spl:26` executes
`bin/release/linux-x86_64/simple_lsp_mcp_server` -- a **prebuilt binary**. It
stayed green through both sabotages. That is correct for the
production-cached-artifact rule (which must not be regressed), but it means
these specs cannot detect a source-level framing regression. Any future framing
change must be proven by a from-source run, as above. This is the difference
between a merge that compiles and a merge that runs.

`test/02_integration/app/mcp_stdio_integration_spec.spl` fails 1 of 3 both
before and after this change -- pre-existing, unrelated, unchanged.

## Not done, per-site reasons

- **B, C** -- real behavioural divergence (above). Each needs its own spec of
  its *current* behaviour before it can be moved; C additionally needs a
  decision on whether its single-line read is a bug to fix or a constraint to
  keep.
- **D, E** -- different type discipline and different substrate.
- **`examples/10_tooling/**`** -- live source, but standalone example programs
  with no import path to `src/app/protocol/`.
- **`config/mcp/mcp_startup_lib.shs`** -- 388 lines, **zero executable
  references**, usage comment names a nonexistent `.sh` file, built on the
  abandoned `.smf` source-compile model. Confirmed obsolete; deliberately NOT
  wired.

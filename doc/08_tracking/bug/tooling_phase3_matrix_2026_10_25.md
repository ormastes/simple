# Phase 3 tooling matrix continuation — 2026-10-25

This adds independent findings to the existing Markdown repair report; it does
not reset its exhausted six-attempt budget. Same isolated worktree and producer
hash as `md_lsp_phase3_native_repair_2026_10_25.md`.

## LSP MCP attempt accounting

Six native-build attempts total, including the previous turn:

1. Default LLVM route: runtime symbol inspection failed.
2. GNU/Cranelift route: missing `rt_host_memory_headroom_bytes_v1` at link.
3. Explicit actual provider, Cranelift: link succeeded; real initialize panicked
   at the POSIX-only SOSIX console gate on Windows.
4. Checked byte-transport repair, Cranelift: link succeeded; a real frame header
   was written but response-body write rejected. ASCII control also failed.
5. Same repair, LLVM: link and actual framed and JSONL protocol exchanges passed.
   Unicode/string/numeric-zero IDs were preserved; tools/list returned 13 tools.
6. Content-Type-first requests previously selected JSONL and emitted an extra
   method-not-found error. Repaired header detection; the final LLVM binary
   returned exactly the two expected framed responses around an initialized
   notification, with 13 tools and exit 0 (15 ms whole exchange).

The LSP lane's six-attempt repair/build budget is exhausted. Do not reset it by
renaming the feature or worktree. LLVM success does not qualify the failed
Cranelift owner path. Logs and
wire captures are retained under `build/tooling-check` and as
`simple_lsp_mcp.*.log` at the worktree root.

Definition and hover were exercised on a real tiny source fixture using the
LLVM executable and explicitly pinned local compiler. Both returned
`command failed with exit code -1: missing command` as ordinary MCP content,
without `isError`. These are functional failures. Diagnose the command/env ABI
boundary and propagate typed execution failure; do not classify arbitrary
successful content by matching an English error prefix. Existing handlers also
spawn raw query source and need a cached-native/in-process owner review.

## T32 entrypoint distinction and failures

`src/app/t32_mcp_server/main.spl` is a startup/readiness facade. With the explicit
provider it links and exits 0 but writes a banner instead of serving MCP. It
cannot establish server protocol correctness.

The actual server entry is
`examples/10_tooling/trace32_tools/t32_mcp/main.spl`. Attempt 1 refused missing SCV
compile-event journal. Attempt 2 used the documented cold-initialization switch
and collected HIR failures (204 errors reported, 117 sources claimed). Imports
are unresolved across the physical tooling namespace and `t32_mcp` facade;
retain `t32_actual.cold-init.log` for exact diagnostics. No hardware operations
were executed.

Actual T32 CLI: one native-build attempt, HIR aggregate failure over 80 sources.
First concrete missing type: `McpT32Session` in the CLI bridge. Retain
`t32_cli.native.log`.

CMM LSP: one native-build attempt, reaches MIR and fails with ambiguous
`check_classic_not/and/or/xor` and unresolved parser methods `check_op`/`advance`.
Retain `cmm_lsp.native.log`; do not silently rewrite accepted grammar to avoid
the compiler's receiver-resolution failure.

## Inventory and live prerequisites

Canonical `phase3-test-inventory.shs discover` failed because `.spipe/spipe` is
uninitialized in this isolated checkout. The resulting empty file is NOT a
validated zero-test inventory and is not a receipt. Initialize nested owners
without mutating another active session's checkout before repeating discovery.
Full phase object/link inventory and aggregate verification remain outstanding.

Native test-runner build attempt 1 SUCCEEDED (terminal exec session 99786), output
`build/tooling-check/test_runner.exe`, log `test_runner.native.log`, exit record
`build/tooling-check/test_runner.exit`. MCP corrected LLVM/provider attempt 2
SUCCEEDED (terminal exec session 2293), output `build/tooling-check/mcp.exe`, log
`mcp.llvm-provider.log`, exit record `build/tooling-check/mcp.llvm-provider.exit`.
The MCP binary's actual initialize/tools-list smoke FAILED immediately at the
Windows SOSIX output gate (exit 1, zero stdout, stderr `panic: SOSIX ordinary U`).
It is linked, not a working server. The producer's internal native compiler
still logs serial object generation; independent target processes ran in
parallel. This is not proof of parallelism inside a target or of all phase rows.

The built runner was invoked once on the Markdown parser SSpec with explicit
LLVM backend, source roots, pinned producer and runtime, sequential execution,
and retained artifacts. It failed before test compilation:
`owned Windows temporary root unavailable`. Its summary counted one infrastructure
failure; zero of the four authored examples are proven executed. A secondary
test-db command also failed with `missing command`. Retain `md_lsp.sspec.log`.
Repair the Windows process/temp-root owner before retrying suites. The LSP
stdio SSpec remains UNRUN, rather than repeating the same infrastructure failure.

SSpec changes are authored, not executed: exact selected native binary,
unbridged stdout, unique input directory, bounded process, strict stderr/exit
checks, multilingual framed ID, and repaired malformed opening docstring in
the log-mode spec. Manuals must not describe these as passing until execution.

STATUS: FAIL — protocol transport improves on LLVM; functional and suite gates
remain incomplete. No PR merged, no release qualification claimed.

## Subsequent independent repairs and inventory recovery

Evidence correction (2026-10-25): earlier PowerShell-piped Python scripts used
non-ASCII source, which PowerShell 5 can replace with question marks. Their
Unicode-specific claims below are not accepted as Unicode proof. ASCII transport
observations remain valid. The replacement candidate checks described below use
ASCII Python source and explicit Unicode code points.

MCP build attempt 3 uses `app.protocol.wire_stdout`, a checked UTF-8 byte-output
owner, instead of the Windows-rejecting SOSIX ordinary console gate. Its actual
LLVM binary passed these distinct native criteria:

- JSONL initialize/initialized-notification/tools-list: exactly two replies,
  preserved IDs, 176 real tools, exit 0, empty stderr (31 ms whole exchange).
- `simple_read`: actual multilingual Markdown file contents returned, exit 0,
  empty stderr (15 ms whole exchange).
- Content-Type-first framed initialize/notification/read: valid byte lengths,
  Unicode ID preserved, no notification reply, actual contents returned, exit 0,
  empty stderr (94 ms whole exchange).

Artifacts: `mcp.wirefix.native.log`, `build/tooling-check/mcp_wirefix.exe`, and
`mcp.wirefix.*`, `mcp.read.*`, `mcp.framed-read.*` captures under that directory.
These are small-fixture observations, not full startup/request/RSS qualification.
The earlier failed MCP binary/console evidence above remains historical evidence.

Nested repositories were initialized in this isolated checkout at exactly the
parent's pinned commits, without changing the shared checkout's nested work:
`.spipe/spipe` at `0a00354eeea87ab7a74ef6e1aa3b8d5756bc1b75` and the CUDA
example at `7126ab5d530fb30d712998b0086193483783a5af`. Canonical discovery and
summary now succeed. `phase3-test-inventory.summary` reports 4121 planned library
rows, 527 tool rows, 6 nested rows, and 2 docs rows. These 4656 planned rows are
NOT executed tests or passing examples. Full phase object/link execution is
still incomplete.

Independent T32 audit found a current-source resolver gap, not solely a stale
producer. Physical fallbacks now cover `app.mcp_t32` and `app.cmm_lsp` after
ordinary probes, preserving prefix boundaries and closure alias registration.
The existing resolver spec now checks actual session-state/type/parser owners
and similarly named negative prefixes. Source and tests are statically reviewed,
UNRUN. Actual T32 consumers need a rebuilt compiler producer and real Hello
compile/run sanity first. CMM receiver ambiguity remains a separate failure.

Windows resource-owner work reached six attempts and is recorded in
`windows_owned_scope_admission_2026_10_25.md`. TEMP lookup and recursive directory
creation advanced, but native child admission still rejects environment data.
Do not repeat blocked suites or claim examples passed from infrastructure counts.

## MCP envelope candidate and landing gate

The sixth MCP native attempt compiled and linked `mcp_envelope_candidate.exe`
with exit 0 and peak process-tree RSS 4165396 KiB. It parses root JSON-RPC fields
with the shared tokenizer, preserves lexical request IDs, suppresses notification
replies, validates nested JSON grammar, and decodes extracted string values once.
Context-tool consumers no longer decode those values twice.

Actual native checks passed: notification suppression (including a nested client
ID), null-ID rejection, nested-method isolation, escaped root key/method dispatch,
exact large integer ID, malformed-message recovery, and real Korean file paths
with both raw UTF-8 and escaped JSON strings (8 cases). A separate Content-Type-
first framed request preserved a genuine 10-byte Korean/emoji ID and exact byte
length. Captures: `build/tooling-check/mcp-envelope-wire-results.json`,
`mcp-envelope-framed.stdout`, and `mcp-envelope-final/`.

These direct wire checks do not replace SSpec execution. The 12 production-parser
SSpec examples and integration suite remain UNRUN because native child admission
is blocked. Core compiler/lib/MCP/LSP checks remain incomplete. Both frozen
compiler and full-CLI rebuilds terminated at the enforced 12 GiB cap (exit 88,
peaks 12623744 and 12608500 KiB); neither produced a qualified replacement.
The working/staged direct-env guards passed, and doc/06_spec contains zero
executable specs. Generic tool-parameter key scoping remains a separate concern.

STATUS: FAIL for landing admission. Focused MCP wire checks PASS; mandatory
compiler, suite, and full-tool functionality gates have not passed. Do not merge
over these missing gates or describe authored SSpec examples as executed.

## Remaining envelope checks and concrete JSONL defect

Continuation of candidate-six verification (no rebuild): eight additional wire
cases passed: duplicate escaped ID, duplicate method, fractional/boolean/object
IDs, trailing JSON token, scalar params, and a quoted/backslash string ID.
Evidence: `build/tooling-check/mcp-envelope-extra-results.sdn` and associated
captures. These are direct native checks, not executed SSpec examples.

One additional case FAILED: JSONL `[]` followed by EOF returns exit 0 with no
reply instead of Invalid Request. `_mcp_read_message` at main.spl's JSONL branch
recognizes only lines starting with an opening brace; it consumes other JSON
values as if they were headers. The same `[]` sent with Content-Length framing
returns -32600 correctly, isolating the defect before envelope parsing.
Removal criterion: real native JSONL invalid-root array/scalar inputs receive
the appropriate error and a subsequent valid request still dispatches; framed
traffic remains intact. The exhausted six-cycle MCP budget prohibits another
repair/build retry without the requested explicit extension. Keep the PR draft.

## Independent T32/CMM object collection

While compiler cycle five remained live, two bounded native object diagnostics
used separate source-owned caches and enforced 2097152 KiB caps, LLVM and the
pinned local stage-three producer. CMM lexer compilation succeeded: exit 0,
peak 259812 KiB, `build/tooling-check/cmm_lexer.o` 54025 bytes, with real code
symbols. Its two-source closure completed; this is not a linked CMM server or
executed lexer/SSpec regression. Evidence: `cmm-lexer-object/`.

T32 MCP `json_helpers.spl` object compilation failed before object emission:
exit 1, peak 355516 KiB, 54 HIR sources, one poisoned module. Root diagnostic:
unresolved `rt_process_run` at line 328 in `t32_shell_cmd`. That helper also
hardcodes `/bin/sh`, shell `export`, and `/dev/null`, so adding an import alone
would not prove Windows execution. Repair must use the platform process owner
and preserve stdout/exit/error semantics; verify a real bounded command on
Windows and POSIX, then the actual T32 MCP handler. Evidence: `t32-json-object/`.
No diagnostic policy or environment/process guard was disabled.

Conservative T32 campaign accounting is six diagnostic rows: CLI, actual MCP,
CMM server, current-resolver probe, CMM lexer object and T32 helper object.
No further repair/compile retry in this lane without an explicit budget
extension. These results do not narrow the still-incomplete full phase matrix.

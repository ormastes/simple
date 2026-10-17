# OPEN: LSP MCP text output crossed the tagged-value printing ABI

The native LSP MCP server returned decimal pointer-derived output instead of JSON. `json_helpers.spl` declared `print_raw(text)`, while the selected C provider implements `print_raw(int64)` as tagged-value printing. GDB observed the call carrying a raw pointer beginning `{"jsonrpc":"2.0"`. Exit zero was not protocol success.

## Repair and boundary

Import the existing text-printing alias through a narrow SOSIX stdio module. Its `diag.print_raw(text)` delegates to `rt_print(const char*)` in the qualified hosted C provider. Flush exactly once after each complete JSONL or Content-Length frame, using the existing stdout flush owner. Generic value printing is unchanged. No pointer probing, reinterpretation, entry alias, stub, or runtime replacement is introduced.

The source bytes of both production owners exactly match the executed final candidate. The latest release base still contained the mismatched extern and lacked the narrow module; no upstream implementation was replaced. The final executable also included three unrelated compiler repairs in its source projection; they are not included in this PR. Full source/producers/runtime/backfill/wrapper hashes are in the adjacent evidence JSON.

## Actual executed evidence (Linux hosted C provider)

Baseline strict-linked executable exited zero but emitted `1391917173973013919171777716\n` (28 bytes), failing JSON validation. Importing the entire SOSIX host facade then hit resource stop 88 at 6,311,632 KiB peak RSS; that dependency expansion is a concrete performance limitation, not a controlled benchmark. The final narrow facade avoids that whole-closure import and completed compilation in 45.1474 seconds (260,800-byte object). Strict paired-runtime/backfill linking exited zero (2,319,968-byte executable).

The original Linux protocol harness executed JSONL and Content-Length separately: two initialize/tools-list responses per mode, four valid responses total, stdin held open during both responses, nonempty server name/tools, exit zero and empty stderr. Times were 3.423 ms and 4.504 ms for these small local sessions, not representative load benchmarks. The unchanged C value-printing regression executed `42` and `-7` and produced exactly `42\n-7\n`, exit zero, empty stderr. All three native repair cycles are exhausted; packaging did not repeat them.

The exact executed Linux harness is retained under `test/02_integration/app/fixtures/` as provenance only; its original artifact-relative binary path is unchanged. The portable harness `test/02_integration/app/lsp_native_stdio_protocol_test.py` requires `--binary ABSOLUTE_PATH --receipt OUTPUT_JSON`. It preserves the two-request/two-mode protocol engine and adds cross-platform pipe threads, bounded output, explicit checks, digest binding and failure on unexpected trailing output. The portable harness passes Python AST parsing. Root independently executed it against the retained broken baseline: exit 1, both modes rejected with zero valid responses despite child exit zero. Each timed out with stdin open and detected trailing invalid output after shutdown. Its **positive path remains UNEXECUTED**, and Windows behavior is unqualified; the original positive harness was not repeated. The C integer regression is an exact copy of the executed fixture.

## Limits and acceptance still required

Status remains OPEN / DRAFT. Required compiler, lib, MCP and LSP checks, the MCP integration SSpec, core runtime smoke, and full MCP native smoke remain unavailable with an admitted current producer. No SSpec wrapper was added: a source-runner wrapper would not establish this native ABI or execute the explicit binary. The native harness is the real future executable protocol gate.

The selected C path uses `fputs`, so literal embedded NUL truncates; JSON wire data must escape control characters. This is not a general counted-text NUL repair. Rust's export named `rt_print` accepts `RuntimeValue`, so these C results do not qualify the Rust provider. Pure-Simple/SimpleOS ownership remains unqualified. Windows/macOS/FreeBSD are unexecuted even though the test harness avoids POSIX-only pipe selection. No global performance, memory, cross-provider, or full-suite PASS is claimed. Unrelated invalid-array-handle diagnostics observed during old-producer lowering remain separate.

Evidence root: `/mnt/c/Temp/simple-phase2-phase4-lsp-latest-20261012`; `qualified-repair.json`, `live-protocol-receipt.json`, `integer-print-receipt.json`, `canonical-link-command.json`, and `final-stdio-candidate.patch`. Independent Astra source review accepted the narrow C route with these limitations and found no immediate P0/P1 in the two-owner repair.


## 2026-10-16: the same boundary remains in Simple MCP

A separate Windows MCP build from frozen c1f630e7a05 with the genuine 0CD6
Phase2 producer completed its 143-module lowering and 123 native COFF objects.
A manual clean link without the inherited FORCE:MULTIPLE option succeeded.
Its local initialize/tools-list session exited zero with empty stderr but
emitted 48 decimal digits instead of framed JSON. The executable SHA256 was
`f119c914e4eab8872a20ac19bb105e318dc4d57868c1f7e846b0908b486bfc02`.
Evidence is retained under
`C:/dev/simple-bootstrap-storage/phase3-validation-20261016/phase4-mcp-0cd6-c1f6-cycle1/`.

The MCP entry still declared `extern fn print_raw(s: text)` against the tagged
value C provider. The isolated source repair uses the existing narrow SOSIX
text alias and flushes once after each complete JSONL or Content-Length frame,
matching the LSP repair. The focused MCP native harness reuses the existing
cross-platform two-mode protocol gate with an explicit executable and the
complete static tool set. Its responses must arrive while stdin remains open.
This section records the actual broken baseline; repaired protocol execution
and broader tool qualification remain pending until evidenced below.


### Windows MCP repair executed with an explicit native candidate

Source projection: c1f630e7a05 plus the MCP text-output source fix in
516979176fa. Producer SHA256:
`0cd6d7c598f20af768774d68bc434f6a0b6660f6194a2e34e7eff48946e1aa9b`.
The changed import adds one narrow facade to the closure (144 modules).
The native build completed; its inherited FORCE:MULTIPLE link is retained
only as diagnostic evidence. The qualified candidate uses the same 123 real
SPL COFF objects and a reconstructed clean link with no FORCE, IGNORE, or
unresolved-symbol suppression. Runtime C reuse verifies every source/object
hash and the identical complete runtime/header Git tree, retaining the actual
/Ox /MD core-provider flags. Its canonical entry shim retains the 17 sorted
module initializers from these actual objects.

Clean candidate SHA256:
`58577f0dde65db5d26891c40dc3d773595cdcff74ce09845e1d486ee22963a4b`.
The focused MCP harness passed JSONL and Content-Length: two valid responses
per mode, 176 tools per mode with nonempty text names and no duplicates,
stdin open during both responses, exit zero, empty stderr, and no trailing
stdout. The executable digest was unchanged before and after. The local
sessions took about 55 ms and 43 ms; this is not a representative performance
benchmark. A single held-open negative control against the unchanged broken
candidate failed both modes with zero valid responses and timed out while
stdin remained open; its actual process exit was zero with empty stderr.

Evidence:
`C:/dev/simple-bootstrap-storage/phase3-validation-20261016/phase4-mcp-0cd6-text-fixed-cycle2/`:
`strict-fixed-protocol.json`, `negative-baseline-protocol.json`, and
`manual-clean-link/{clean-link.rsp,link-exit.txt,runtime-reuse-proof.json,cached-objects.json}`.
The coordinator independently reviewed the digest-bound positive receipt and
verified zero unsafe linker options in the clean response.

These results qualify local initialization and static tool advertisement for
this Windows C-provider candidate. They do not qualify delegated CLI semantic
requests, every advertised tool, full CLI/test-runner behavior, the newer
release branch, complete compiler/lib/MCP/LSP checks, package admission, or
local deployment. Those broader gates remain UNRUN. No Rust provider or
additional platform result is inferred from this C-provider execution.

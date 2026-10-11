# OPEN: LSP MCP text output crossed the tagged-value printing ABI

The native LSP MCP server returned decimal pointer-derived output instead of JSON. `json_helpers.spl` declared `print_raw(text)`, while the selected C provider implements `print_raw(int64)` as tagged-value printing. GDB observed the call carrying a raw pointer beginning `{"jsonrpc":"2.0"`. Exit zero was not protocol success.

## Repair and boundary

Import the existing text-printing alias through a narrow SOSIX stdio module. Its `diag.print_raw(text)` delegates to `rt_print(const char*)` in the qualified hosted C provider. Flush exactly once after each complete JSONL or Content-Length frame, using the existing stdout flush owner. Generic value printing is unchanged. No pointer probing, reinterpretation, entry alias, stub, or runtime replacement is introduced.

The source bytes of both production owners exactly match the executed final candidate. The latest release base still contained the mismatched extern and lacked the narrow module; no upstream implementation was replaced. The final executable also included three unrelated compiler repairs in its source projection; they are not included in this PR. Full source/producers/runtime/backfill/wrapper hashes are in the adjacent evidence JSON.

## Actual executed evidence (Linux hosted C provider)

Baseline strict-linked executable exited zero but emitted `1391917173973013919171777716\n` (28 bytes), failing JSON validation. Importing the entire SOSIX host facade then hit resource stop 88 at 6,311,632 KiB peak RSS; that dependency expansion is a concrete performance limitation, not a controlled benchmark. The final narrow facade avoids that whole-closure import and completed compilation in 45.1474 seconds (260,800-byte object). Strict paired-runtime/backfill linking exited zero (2,319,968-byte executable).

The original Linux protocol harness executed JSONL and Content-Length separately: two initialize/tools-list responses per mode, four valid responses total, stdin held open during both responses, nonempty server name/tools, exit zero and empty stderr. Times were 3.423 ms and 4.504 ms for these small local sessions, not representative load benchmarks. The unchanged C value-printing regression executed `42` and `-7` and produced exactly `42\n-7\n`, exit zero, empty stderr. All three native repair cycles are exhausted; packaging did not repeat them.

The exact executed Linux harness is retained under `test/02_integration/app/fixtures/` as provenance only; its original artifact-relative binary path is unchanged. The portable harness `test/02_integration/app/lsp_native_stdio_protocol_test.py` requires `--binary ABSOLUTE_PATH --receipt OUTPUT_JSON`. It preserves the two-request/two-mode protocol engine and adds cross-platform pipe threads, bounded output, explicit checks, digest binding and failure on unexpected trailing output. It has only been parsed with Python AST: **AUTHORED_UNEXECUTED**. Its stricter framing/cleanup paths and Windows behavior are not qualified by the prior harness. The C integer regression is an exact copy of the executed fixture.

## Limits and acceptance still required

Status remains OPEN / DRAFT. Required compiler, lib, MCP and LSP checks, the MCP integration SSpec, core runtime smoke, and full MCP native smoke remain unavailable with an admitted current producer. No SSpec wrapper was added: a source-runner wrapper would not establish this native ABI or execute the explicit binary. The native harness is the real future executable protocol gate.

The selected C path uses `fputs`, so literal embedded NUL truncates; JSON wire data must escape control characters. This is not a general counted-text NUL repair. Rust's export named `rt_print` accepts `RuntimeValue`, so these C results do not qualify the Rust provider. Pure-Simple/SimpleOS ownership remains unqualified. Windows/macOS/FreeBSD are unexecuted even though the test harness avoids POSIX-only pipe selection. No global performance, memory, cross-provider, or full-suite PASS is claimed. Unrelated invalid-array-handle diagnostics observed during old-producer lowering remain separate.

Evidence root: `/mnt/c/Temp/simple-phase2-phase4-lsp-latest-20261012`; `qualified-repair.json`, `live-protocol-receipt.json`, `integer-print-receipt.json`, `canonical-link-command.json`, and `final-stdio-candidate.patch`. Independent Astra source review accepted the narrow C route with these limitations and found no immediate P0/P1 in the two-owner repair.

# Native LSP raw-print ABI mismatch

Status: fixed in an isolated candidate; Linux native regression PASS. Other operating systems not executed.

## Reproduction and actual provider contract

P2 producer SHA256 `892b220e19b5cbafd620190c95b9a2f26fc5ebc08304b8b07d4475da0ea7abb0`, source `523ce4c9b47f81f1472f121bcac84a4238fb5c76`. Baseline LSP object 255616 bytes and strict-linked ELF 2931600 bytes. Native initialize exited zero but printed `119395956` instead of JSON.

Actual caller disassembly called `rt_interp_cstr` at 0x41a074, moved the raw pointer into rdi, then called `print_raw` at 0x41a07c. The fresh C archive alone supplied print_raw from runtime_native.o. Its contract is `int64_t print_raw(int64_t value)` and it delegates to tagged-value `rt_core_print_value_to`; passing a borrowed C string violated that contract.

## Repair and prevention

The app imports `sosix_print_raw` from a narrow SOSIX standard-I/O facade. That facade reexports the existing SFFI diagnostic owner, which invokes `rt_print(const char*)`; this matches the producer's C-string lowering. No runtime provider, compiler rebuild, or link stub is required.

Run `sh scripts/check/check-simple-lsp-native-stdio.shs /absolute/path/to/simple_lsp_mcp_server`. It runs the native binary directly and checks initialize and tools/list response IDs and result fields in both JSONL and exact byte-counted Content-Length frames. A numeric pointer, malformed JSON, missing response, truncated frame, or nonzero exit fails. Existing SPipe coverage remains `test/02_integration/app/simple_lsp_mcp_stdio_spec.spl`; its test runner was unavailable in this bootstrap lane, so no SPipe PASS is claimed.

Linux evidence: corrected object 260704 bytes, compile exit0 in47.153s; strict fresh C+Rust link exit0, ELF2938096 bytes. JSONL exit0 produced6264bytes and framed exit0 produced6309bytes, each two correctly parsed responses and stderr0. Evidence artifacts are `/mnt/c/Temp/simple-manual-lanes-20261011/p2-lsp-sosix-stdio/producer-runtime-binding.json` and `protocol-regression-receipt.json`.

The initially selected broad async host facade exposed a separate link defect: unconditional imported WINDOWS_REDIRECTED_TOKEN_BASE references from process_wait/process_kill/process_is_running lacked a definition in the combined object. The constant exists unconditionally in its source owner; this is not established as an OS selection defect. The narrow facade avoids importing that unrelated process closure. Its repair remains separate.

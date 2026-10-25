# LSP MCP Windows byte transport repair

Scope: repair the compiled LSP MCP stdout boundary without admitting Windows
for unrelated SOSIX console, environment, directory, or process operations.

## Owner and startup path

`app.simple_lsp_mcp.main` dispatches through `json_helpers.write_stdout_message`.
The former `sosix_print_raw` alias passed through an explicitly POSIX-only console
gate. The Windows native binary therefore panicked before returning initialize.
MCP stdout is a protocol byte stream, not a host-console text conversion surface.

`json_helpers` now uses the existing strict UTF-8 codec and checked
`sffi.fs.io_file_write_all` descriptor owner. The existing 16 MiB boundary check
remains before encoding. Encoding and write failures terminate explicitly;
partial output is never reported as success. Descriptor 1 is borrowed and never
closed. The existing owner flush runs after each complete frame or JSONL message.
No new raw extern, shell process, filesystem scan, or platform charset conversion
is introduced on this output path. Windows runtime binary stdio initialization
remains responsible for disabling CRT newline translation.

## Hot requests, indexing, and invalidation

This change adds no cache or index. Each response is encoded once per existing
write call; frame construction and transport-mode selection remain unchanged.
No invalidation protocol is needed for these stateless output operations.

Tool dispatch is independently incomplete: real native definition and hover
requests returned `command failed with exit code -1: missing command` inside
ordinary successful MCP content. The command/query owner and typed error
propagation need separate repair. Do not infer working code intelligence from
initialize or tools/list, and do not turn textual prefix matching into the error
contract. The existing query startup/raw-source fallback path also needs review
against the cached-artifact requirement before admission.

## Verification and performance boundaries

The diagnostic producer is the local Stage 3 compiler recorded in
`../08_tracking/bug/md_lsp_phase3_native_repair_2026_10_25.md`. Its older runtime
inventory omits the current memory-headroom provider. Diagnostic builds use a
separately compiled actual provider through supported `SIMPLE_LINK_OBJECTS`;
shared runtime archives are untouched. This is not a managed release admission.

- LLVM native framed initialize/tools-list: exit 0, two responses, Unicode string
  ID preserved, 13 actual listed tools; measured whole exchange 31 ms.
- LLVM native JSONL initialize/notification/tools-list: exit 0, no notification
  response, numeric zero and string IDs preserved; whole exchange 16 ms.
- Cranelift with the same repair: frame header written, body write rejects;
  ASCII control also rejects. Backend/byte-owner defect remains unresolved.
- Native definition and hover: process exit 0, but both tool results contain
  missing-command failures; those operations FAIL functionally.
- Content-Type-first framing was additionally repaired: a JSON object line
  selects JSONL; other input enters the header loop. The final native build
  returned exactly two framed responses around an initialized notification,
  with 13 tools, exit 0 and empty stderr (15 ms whole exchange).
- Native SSpec runner construction succeeded. Its first native test invocation
  failed before compilation with `owned Windows temporary root unavailable`;
  no Markdown examples passed. The improved stdio spec pins
  an explicit native executable, removes the Node bridge, uses bounded process
  ownership and unique temporary input, and adds a multilingual-ID scenario.

The existing native smoke startup budget is 5000 ms. These small exchanges are
individual observations, not representative request-latency or RSS qualification.
Warm repeated-request targets, realistic fixture scaling, and peak RSS still
require evidence. Mandatory compiler/lib/MCP checks, core/runtime smokes, native
suite results and generated manuals remain admission gates. No release PASS.

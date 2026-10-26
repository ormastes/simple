# Phase 2 tooling feature verification

Status: INCOMPLETE. User selected Phase 2 feature checking while Phase 3 is
unavailable and authorized landing features once they work with Phase 2.
This does not qualify Phase 3 or permit bypassing feature verification.

Frozen initial source: aa3ded114ec, release base bb7fcfa4673 plus the tooling
fixes and modern stdio specs. Isolated checkout:
`D:/dev/simple-tooling-phase2-check-20261026`.

Producer: pure-Simple Phase 2, SHA256
`1ad6ea53c67f3e01efc5c1b0ac8aa4dcef184a0987b4d3c806c59e14e96be584`.
Its matching frozen runtime capsule is under
`C:/dev/simple-phase3-bootstrap-owned/build/bootstrap/phase2-runtime-capsules/`
with that digest. Target Windows MSVC, LLVM, core-c-bootstrap runtime bundle.
The exact producer's provenance/admission and sanity receipts were inspected.
A fresh Hello native build and execution passed (exit0, expected output).
It exposes compile/native-build, not general check/test commands.

## First finite collection

Evidence: `build/tooling-phase2/<row>/` and `matrix.sdn`; separate private
caches, enforced 6GiB caps and 900-second collector bounds per row.

| Row | Current evidence |
| --- | --- |
| MCP | MIR FAILED: inferred token value cannot dispatch contains; shared CodecError payload mismatch; additional non-array loop errors. No link. |
| LSP MCP | MIR FAILED: CodecError payload mismatch; file_text_session byte-array loops inferred I64. No link. |
| Markdown LSP | HIR FAILED: unresolved parser helpers and array type. Uncommitted earlier Markdown repair is preserved in its original checkout, not silently included here. |
| T32 CLI | HIR FAILED: app.t32_cli.mod does not export t32_cli_main. |
| T32 MCP | Source loading FAILED: t32_mcp sibling-qualified imports unresolved by this producer's default roots. |
| CMM | Initial main.spl path absent; corrected server module reaches HIR and fails unresolved print_raw. This is a setup correction, not a server PASS. |
| SSpec runner | RUNNING, exec session7725; source frozen until terminal. No examples executed. |

## Typed Result payload investigation

Bug: `phase2_result_payload_nominal_type_loss_2026_10_26` (open, unproved root).
The shared text-I/O contracts already declare correct Result payload types.
CodecError contains kind, byte_offset and reason; none may be discarded.
Current old-producer diagnostics do not identify which two of six wrappers
caused the identical Codec variant mismatches.

Proposed falsifiable workaround after the live runner finishes: explicitly
type Result call locals and forwarded codec payloads; explicitly type byte-
buffer Result locals and retain array push results. Check actual byte values
and structured error kind/offset before accepting it. Do not replace array
loops merely to conceal I64 inference or weaken errors into strings. Bind the
token tuple's kind/value to text before retrying envelope lowering. A failure
remains a failure; no placeholder passes, guard bypasses or invented test counts.

Landing requires the selected feature's real native behavior and applicable
SSpec/core gates, reviewed exact PR contents, and merge. No feature is yet
admitted for landing from this Phase 2 cohort.


## First collection terminal and typed retry

The SSpec runner terminated with exit139 at MIR entry after its286-module HIR
closure and monomorphization. Peak RSS1827404 KiB; no executable or examples
passed. CMM server also failed HIR on unresolved print_raw. Initial rows are
terminal before source edits; retained logs remain immutable.

Changed-source compatibility attempt two pins token tuple fields to text,
codec Result expressions and forwarded CodecError locals to declared types,
and byte-buffer Results to their concrete sum type. Array append results are
retained. This preserves error fields and byte-loop semantics; it is an
unqualified old-producer workaround until actual values/error regressions pass.
LSP MCP retry: build/tooling-phase2/lsp-mcp-typed, exec session73187, same private
cache owner and enforced limits. No overall PASS or landing admission yet.

## Changed-source results

LSP MCP typed attempt two FAILED with the same Codec payload and byte-array
MIR errors. Removed the ineffective shared text-I/O edits; preserved the failed
log at `lsp-mcp-typed/`. No claim that explicit bindings repaired that owner.

The envelope's separately typed tuple fields compiled in an actual-production-
parser native probe. Executing `mcp_envelope_probe.exe` exited0 and reported
16 input cases /96 actual assertions. This qualifies the focused parser input
set only, not the full MCP consumer or a general SSpec run. Source fixture and
receipts remain in `build/tooling-phase2/envelope-probe/` and its sibling file.

Copied the existing uncommitted Markdown repair into this isolated cohort,
preserving its original checkout. Phase2 compiled/linked the repaired17-module
closure, and initialize/shutdown/exit ran successfully. A real didOpen followed
by documentSymbol returned First/Second headings and correct source lines.
However folding request ID3 and string request IDstring-id both returned ID0.
This is a functional protocol failure, not PASS. Captures:
`build/tooling-phase2/markdown-functional.stdout` and `.stderr`.
Markdown remains unqualified for landing despite compile/link and handshake
success. The same cohort's parser/fence and document-mutation requirements
remain to be verified. No unsupported full-feature readiness inference.

## Markdown request correlation repair

Phase2 Markdown attempt three compiled/linked the19-module closure successfully
(`markdown-ids/`). Wire dispatch now validates the root envelope and carries its
lexical ID to raw response handlers. Existing integer-call interfaces remain
adapters. This removes both string-to-integer coercion and failed optional
numeric conversion defaulting to zero, without accepting nested IDs as root IDs.

Actual native folding requests passed with IDs3, string-id, an escaped quote/
backslash string, integer9007199254740993, and genuine Korean/emoji. The live
document produced two fold ranges for each. Seven responses exactly matched
initialize, five requests, shutdown; notifications produced no replies, frame
lengths parsed exactly, and exit0. Captures: `markdown-ids.stdout`/`.stderr`.
Added3 meaningful SSpec examples for raw success/error IDs and the retained
integer facade; these are authored, not executed by the crashed general runner.
Document changes, parser edge cases, and remaining qualification are incomplete.

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

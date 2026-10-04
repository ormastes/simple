# Static ELF operation binding verification

STATUS: FAIL — full item4 and Phase 4 remain incomplete.

Source scope: structural sealing of typed relocation-field, layout and writer
operations and actual consumption by the production ELF link driver. Existing
public entrypoints retain their result shape and select canonical operations;
an explicit composed entry returns the image with its structural receipt.

The relocation operation must return the bytes the driver actually consumes.
Binding only `reloc_apply` would be decorative because the old driver independently
recomputed patches through `reloc_patch_bytes`. Architecture normalization and
special TLS/RISC-V paths remain driver-owned; the facet name must not imply
ownership of every relocation transformation. Parser binding is not byte-source
binding, and generic layout is not boot-layout admission.

Tests are to establish canonical output parity with independent fixture oracles,
observable selected-operation dispatch, selected callback errors, malformed
result rejection and missing/duplicate/inconsistent facet rejection. Source
ordering establishes test-first intent only; actual RED/GREEN remains UNRUN.

Structural policy describes an in-process, single-call, noncritical binding.
Zero reservation fields are no reserved accounting, not a zero-memory claim.
Neither the seal nor its declared version digest proves artifact signatures,
immutable mapped identity, GC behavior, memory enforcement or measured RSS.
Callbacks are trusted in-process code; this is not an untrusted plugin sandbox.

Native Simple compilation/tests, canonical docgen, coverage, core/lib/MCP checks,
native smoke and NFR measurements remain UNRUN. The inspected deployed release
runtime directories remain absent. No additional capped runtime build was run.

Integrated outcome: two production files route existing entrypoints through
the sealed owner; the explicit entry returns image plus composition receipt.
Eleven scenario declarations cover canonical real fixture output, each selected
operation, provider reordering with exact receipt slots, shifted header symbols,
strip/retained-root behavior, missing/duplicate/mismatched offers, callback errors
and malformed results. The initial four executable test intents preceded core
implementation; followups extend coverage and capture review findings.

Source review found a writer-contract gap and the implementation now compares
all program-header fields and relevant section metadata with the selected plan.
A real serialized-image mutation regression changes one PT_LOAD address and
requires rejection. Root and independent reviews found no remaining P0/P1 in
the core and primary acceptance changes. LLVM fixture construction/inspection
succeeded; this is not Simple runtime evidence. Authored manuals remain UNRUN.

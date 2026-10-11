# Block compiler native contract repairs

Status: pending self-hosted and Phase3 qualification. Do not treat bootstrap
seed probes as production verification or release admission.

## Original Linux failure

Frozen source 3e6da6a19a3a3ad0f11e2d6419dcd1dcdc06d5ba had no pending
agent feature changes applied. Canonical Stage2 exited1 after2075.68s:
1248 modules compiled, highlighting and testing failed. No qualified Phase2
binary, Hello execution, Phase3 or MCP resulted. Failed receipts and native
objects remain under /root/simple-phase3-linux-3e6-seed-20261012/bootstrap.

## Repairs on current release_phase3

Base ffbf2320693dfe22ea67112034b0a639aa40b0ac. Highlighter binds real
Optional block delimiters, handles -1 search results and empty keywords,
uses existing text length methods, and finds LF comment boundaries with
index_of. BlockDefinition parse methods and all affected adapters return
Result<BlockValue,BlockError>; simple callbacks return Result<BlockValue,text>.
The plugin text-handle ABI adapts to Ok(BlockValue.Raw(text)); null-handle
failure stays unchanged. Const evaluation returns ConstValue? consistently,
and test_no_const_eval binds its real present payload. Error span helpers use
a real (i64,i64) tuple parameter and import the actual error constructor.

## Actual finite probe results

All probes below use the explicitly recorded Rust seed, core-c-bootstrap
runtime and Cranelift backend. Stub fallback is disabled. They are bootstrap
diagnostics, not self-hosted application tests.

- Highlighter source cycle1: unresolved text_len linker references.
- Highlighter source cycle2: compiled8 modules and linked, exit11 on LF end.
- Highlighter source cycle3: compiled8 modules, linked and executed exit0,
  BLOCK_HIGHLIGHTER_PRESENCE_PASS checks=13. Binary SHA256
  3e951ebe1d16681da831e6ad64b541de4c8e1e239096a2b494fbf8fe3205fe2e.
- Parser cycle1: compiled23 modules, failed2: dangling has_result and a
  bogus module-global [i64,i64] value used as a type.
- Parser cycle2: compiled25 modules, failed0, but linking failed on
  compiler__blocks__blocks__definition__BlockDefinition_dot_parse_payload.
  Real trait-dispatch fixture remains pending; no substituted concrete call.
- Registered nil/present const-evaluation fixtures are authored, unexecuted.

Diagnostic launcher pre-execution failures are retained separately: missing
SCV cold initialization, then an interpreted-driver dispatch terminated at
397.69s. The corrected launcher explicitly selects Rust native build only
for bootstrap diagnostics and retains real identities.

## Open language and qualification defects

The original compact text[i] != '\n' line-comment comparison failed the real
native LF assertion. Its lowering/ABI cause is unproven; do not declare the
language form invalid or the compiler repaired. The index_of implementation
also avoids repeated byte comparisons while preserving LF-exclusive offsets.

Abstract trait parse dispatch remains an unresolved bootstrap-seed link
boundary. Recheck with the newly built self-hosted producer before attributing
it to a specific compiler owner. Preserve the typed trait fixture.

The exact new compiler must compile and execute Hello before descendants.
Phase3, full CLI, core checks, MCP/LSP and interface fixtures remain required
before landing. No PR or release admission is claimed by this document.

Evidence roots: /root/simple-block-repair-diagnostic-20261012 and
/root/simple-phase3-linux-3e6-stage2-20261012. Canonical retry launcher is
prepared in build/review/item5-block-repair-linux-canonical-20261012.py but
has not been launched. The user reactivated the goal; the scoped review evidence above remains unchanged.

## Upstream reconciliation

Rebased onto a55e3c3a67d release_phase3. Kept newer typed lex/hover/signature
contracts, complete Span fields and canonical imports, real test contexts, and
position-aware highlighting search helper. Retained only additional empty-keyword,
LF-boundary, consistent callback and presence-binding repairs. The changed
highlighter helper requires a new native regression; prior13 checks describe
the earlier implementation only. No trait failure was bypassed.

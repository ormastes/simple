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


## 2026-10-12 executed evidence and owner diagnosis

The notes above are historical checkpoints. Current upstream is5b1620525c6
(previous a55e compiler tree unchanged; newer release documentation only).
The highlighter regression on rebased63467f2716c passed13 actual assertions:
`/root/simple-block-repair-diagnostic-20261012/highlighter-rebased`, binarySHA256
90e57b91c5eaedfa410e9c6fa1a20efd3be482c0feff499f1a9ec78c11063b0b.
This remains bootstrap-seed evidence only.

The canonical seed/runtime attempt for63467f2716c completed exit0 in1475.41s,
peak process-treeRSS3001284KiB, no resource stop, quiescent1. Its receipts are
`/root/simple-block-repair-canonical-20261012/seed`; no Phase2 or Phase3 PASS
is implied. The matching native-all, hosted runtime and compiler backfill were
built through the canonical wrapper. Source must be requalified after repairs.

Both real parser and annotation-only diagnostics fail the same abstract
BlockDefinition.parse_payload link. HIR let bindings lose declared trait
identity after the trait aliases to Any; explicit parameter dispatch retains
its slot. A returned-local metadata repair requires defining-module identity,
including same-short-name imported traits with different slot layouts. The
first raw-name-only candidate was rejected during review; it was never applied.

Both original optional registry fixtures executed and crashed before assertions.
Their class-parent syntax is unsupported; use struct trait declarations. The
corrected struct diagnostic allocates a real object with a valid probe vtable,
but crashes later when initializing builtin blocks. Builtin methods declared in
separate inherent impl blocks are omitted from synthetic trait tables, leaving
a null kind slot. Retain actual method ownership and imported declaration/default
authority when repairing this; AST-only imported trait lookup was rejected in
review because per-file native builds retain imported declarations separately.
The fixture syntax correction alone is not a registry-crash fix.

Failure evidence: `/root/simple-return-trait-diagnostic-20261012/{original,annotated}`,
`/root/simple-block-optional-diagnostics-20261012/{absent,present}`, and
`/root/simple-block-optional-struct-diagnostics-20261012/{absent,present}`.
No unchanged failing probe is rerun. Native regression execution with a newly
built repaired producer, real Hello, Phase2/Phase3 and required core/MCP checks
remain pending. No changes from this repair lane have landed.


## Follow-up executed evidence and narrow repairs (2026-10-12)

Source 0596863c905a26566072da7c5f165a8dc20d130d completed canonical Rust
seed/runtime build (exit 0, 785.24 seconds) at
/root/simple-block-repair-canonical-next-20261012. Native Hello compiled and
ran successfully: seed-hello-prepared records two checked cases. The initial
Hello attempt lacked its required artifact directory and performed no checks;
its failed receipt remains intact.

Native collection /root/simple-block-next-regression-zpqdp5cv finished four
passing and three failing rows. Both registry cases, returned-trait dispatch
(six values), and missing-required refusal passed. Parser and separate-method
fixtures compiled but crashed; cross-module extension compilation refused.
Structural collection rust-structural-tests under the canonical output
records returned_trait 1 PASS and implicit_trait 6 PASS / 1 FAIL.

Parser diagnosis: shorthand struct trait implementations were absent from
native-project layout inventory. Constructor stored a vtable header while
receiver copies omitted that header, loading the wrong closure field.
Repair registers shorthand implementations with the existing canonical
vtable-owner resolver and tests receiver-copy header preservation.

Separate-method diagnosis: the trait call returned 111, then assert(bool)
was suffix-aliased to libc __assert. Repair lowers unshadowed statement
assert calls through existing HIR assertions and rejects reserved platform
suffix owners. True, false, and declared-callable fixtures are added.

The extra cross-module inherent-extension positive expectation was unsupported
on the retained old producer too (compile 0, run 139). Preserve original
failures and the positive future fixture; separately test exact safe refusal.
See native_cross_module_inherent_trait_2026-10-12.md. This is OPEN, not a
claim of cross-module support.

These follow-up layout/assert repairs are authored and unexecuted at this
snapshot. Phase2, Phase3, full-CLI/MCP qualification and landing remain pending.

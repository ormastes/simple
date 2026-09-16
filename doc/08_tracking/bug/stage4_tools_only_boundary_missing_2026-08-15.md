# Stage-4 tools-only artifact boundary was documentation-only

## Status

Preparatory implementation restored and reviewed; live migration/admission is
still deferred by the selected baseline gate. Rust-seed results are diagnostic
only.

## Reproducer

Repository search found `CompilerArtifactManifestV1`,
`ToolingLinkReceiptV1`, and `compiler_sources_compiled = 0` only in design and
the documentation-contract system spec. No production module or bootstrap
entry validated the Stage-3 archive/interface/runtime authority, rejected
compiler traversal, or emitted a tooling link receipt.

## Root cause

The stage split was designed while migration remained gated on one admitted
legacy bootstrap, but the production artifact boundary had not been created.

## Restored preparatory boundary

The authorized pure-Simple contract module, Stage-4 wrapper, unit contract,
and wrapper integration contract were restored after accidental removal. They
are retained as preparatory implementation and must be included in review and
frozen-input regeneration; their presence does not open the migration gate or
claim Stage-4 PASS.

Review removed an unintended backend-policy override. The module and wrapper
now require a nonempty backend identity and bind it to the exact unchanged
canonical Stage-3 admission receipt; they do not select LLVM, Cranelift, or a
new Stage-2/Stage-3 default. The wrapper remains fail-closed on receipt/artifact
hashes, Rust-seed identity, compiler-source paths, duplicate units, contained
cache/publication paths, tool smokes, and atomic publication.

`sh -n scripts/bootstrap/stage4-tools-only.sh` passes. The unit/integration
SSpec descriptions now use `should` behavior names and explicit `step(...)`
flows; both system specs carry the required `# codex-system-test` tag. All five
SPipe manuals are restored under `doc/06_spec` and explicitly label live
execution/docgen as gated. Pure-Simple execution remains blocked until an
admitted production runner is available; the Rust seed is not substituted.

## Post-gate implementation requirements

After the current pipeline records one admitted success, wire tool discovery
and compilation through the exact admitted Stage-3 compiler. Derive the
journal from observed compilation, canonicalize paths and dependency closure,
prove `stage4_compiler_files=0`, bind the legacy/Stage-2/Stage-3 receipt chain,
and emit a fully revalidatable `ToolingLinkReceiptV1` including units, reuse
bytes, elapsed time, and peak RSS. Independent fake/stale/source/archive/
interface/runtime-ABI sabotage must fail before compilation.

A Rust-seed mini-build may inventory tool-owner compile failures only when it
uses a distinct `build/mini_cache_stage4_*` cache and is labelled diagnostic.
It can never produce `Stage3AdmissionReceiptV1` or satisfy this bug's PASS.
Final acceptance requires tool objects and `ToolCompileJournalV1` from an
admitted pure-Simple Stage-3 compiler, successful atomic publication, both
live tool smokes, and receipt revalidation against the exact manifest/journal.

Provider token usage and comparable completed-bug average: unavailable.

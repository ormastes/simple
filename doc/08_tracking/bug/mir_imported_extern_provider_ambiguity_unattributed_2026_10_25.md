# MIR duplicate imported-provider diagnostics lack owner context

Status: diagnostics-only patch source-reviewed, native-compiled, and the
standalone ordinary-run diagnostic **PASS: 3 cases, 52 assertions**. The three
SSpec cases and interpreter validation remain **UNRUN**. The six-cycle MIR
diagnostic verification budget is exhausted; no further attempt is permitted.
No codec retry, producer rebuild, or repeated 125-module probe occurred.

The retained Windows core-C fixture attempt used producer
`2cc51dc392b19a3f2fceffcac2d42d0b54fd32caf87eea7c69302656633ac7a7`, source
`79c29f149456f331ef2648721307d596dd40146f`, 24 jobs and a 5,859,375-KiB guard.
MIR reported 125 modules, 22 succeeded and 103 failed. Actual native exit was 1,
peak RSS 3,917,484 KiB and quiescent 1. No fixture executable ran.
Evidence: `C:/dev/simple-llvm-flags-corec-fixture-storage-20261025/compile`.

Both ordinary and flat-bootstrap imported-extern guards reject a repeated
canonical provider owner, but the previous identical message omitted the
importer, conflicting provider rows and raw source origins. The actual log
cannot identify which pair collided. Streaming HIR aliases and post-mono
independent alias tables are a candidate cause; no source-name/path-only dedup
is justified by that observation.

The patch preserves both fatal guards, the error prefix, and existing function
signatures. New named context entrypoints receive actual importer context.
Ordinary diagnostics include the importer name/path, canonical owner key and
both provider array indices/names/paths. Flat-bootstrap diagnostics include the
actual stored names/indices and explicitly mark paths unavailable: that store
does not retain separate path fields. No HIR schema, cache authority, configured
variant/family selection, signature proof, provider choice or lowering policy
changes.

The focused spec builds real parser/HIR declarations and imported function
symbols, checks the duplicate-owner fatal diagnostic and exact row indices,
exercises the unchanged two-argument entrypoint, and includes a unique-provider
control. These three SSpec cases are authored, not runner-qualified. The
standalone fixture reuses their actual parser/HIR setup and checks through
counted native assertions. The flat-bootstrap branch has source review and
native compilation only; no flat-store execution claim is made.

## Retained standalone evidence and fixture corrections

The immutable bootstrap-only producer was
`5a6a8bec8c8c205b2c4507768acf553b3ef6027018706357350394af09f81622`, target
Cranelift/core-c-bootstrap, 24 jobs and a 5,859,375-KiB guard. Header readiness
checked 29 actual C source dependency graphs and 64 files, including platform
headers. The first build compiled 520 modules; subsequent changed-fixture
builds compiled two and reused 518 through the normal retained cache.

Cycles 1-5 exposed fixture setup issues before the MIR guard: an opaque failed
assertion, a logical-name expectation where ParserModule/HirModule retain raw
source filenames, and missing imports. The final context observation showed
an empty parser AST and zero symbol rows, with the explicit HIR semantic API
working. `flat_ast_to_module` intentionally returns an empty module for
nonentry source filenames when the executable inherits `SIMPLE_BOOTSTRAP=1`.
No symbols were fabricated and the nonempty-import assertion was preserved.

Cycle 6 ran the existing cycle-5 binary once in ordinary test context
(`SIMPLE_BOOTSTRAP=0`). Its build remained bootstrap-only; no binary was
rebuilt, no cache changed, and no entry/closure/Stage4 marker was forged. The
actual parser then produced imports and all three cases completed all 52
assertions, including the fatal duplicate-owner diagnostics, compatibility
entrypoint and unique-provider control. Output was exactly
`mir-imported-extern-owner-diagnostics cases=3 assertions=52\n` (60 bytes).
Raw/native exit 0, quiescent 1, no job remnants, cleanup not needed, peak RSS
29,720 KiB. The production three-file patch remained unchanged throughout.

Final evidence:
`C:/dev/simple-mir-extern-ordinary-cycle6-storage-20261025/{evidence,run}`.
Program SHA-256:
`6e352bf2c826f86e05686c51126c1912c35420ee5947463487c5b799865d610d`.
Input manifest SHA-256:
`e8cb77409b3ee9436ec26e2c7dde10301acda9672a72a23bdfac8055ea4bc812`.
This is ordinary execution of a bootstrap-built diagnostic, not a Pure-Simple
producer/descendant qualification or resolution of the original 125-module
alias conflict. All earlier failed receipts and exact fixture versions remain
retained in the numbered private diagnostic storage directories.

The separate retained HIR cache decode refusal (`nil_in_non_optional_scalar`,
fixture bytes 32285, wire line 3238/3440) remains a real store-admission defect.
It was nonfatal in this attempt: HIR retained the uncached module and continued
to MIR. Its exhausted codec cycle budget is unchanged.

Patch source base: `e0837cb030e52793deb944fe9f0d16a29665b46c`. Any diagnostic
probe requires a producer actually containing this patch, pinned source/runtime
identities, normal caches/resource bounds and root review before launch. A
later semantic repair must distinguish issued aliases from genuinely distinct
providers and preserve configured GC/concurrency and preprocessing variants.

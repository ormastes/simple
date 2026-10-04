# Bounded ELF common-symbol verification

STATUS: FAIL — full item4 and Phase 4 remain incomplete.

This slice implements existing common-symbol semantics in the file-backed
stream linker: coalescing, precedence, aligned writable zero storage and real
relocations, retaining read/output/scan/scratch limits. It must not allocate a
resident symbol table or a common-sized buffer. Logical limits do not prove
whole-job RSS enforcement; UnsupportedBudget remains required in production.

Test intent precedes implementation. Runtime execution, canonical docgen,
coverage, compiler/lib/MCP checks and NFR measurements are UNRUN pending an
admitted self-hosted runtime. Prior capped build diagnostics are not repeated.

Source result: the stream resolver retains the canonical first common record,
merges maximum size/alignment independently, and prefers strong regular over
common over weak regular definitions. Layout computes a checked writable tail;
relocations rescan the same allocation order. Emission uses existing zero-fill
windows. Extra table/symbol scans consume the finite work budget and preserve
cancellation. This increases scan work; no runtime performance result is claimed.

The fast archive closure now records definition rank and distinguishes genuine
undefined demand from tentative demand. A selected common provider changes the
demand immediately, avoiding extra common/weak extraction while allowing strong
replacement. Independent review found no P0/P1 in either implementation.

GNU ld 2.46 fixture experiments executed in the research worktree establish the
external semantic oracle: undefined references extract common-only members;
existing common definitions extract strong regular members but not weak or
common-only members. This is not execution of the Simple implementation. See the
source-backed design `doc/05_design/compiler/linker/stream_common_2026-10-04.md`.

Eight authored scenarios cover allocation/independent maxima, common-only
archive extraction, strong and weak precedence, archive nonselection and strong
replacement, a common declaration selected through another symbol, malformed
declarations, and quota/cancellation behavior. Their real relocated pointers are
translated through PT_LOAD metadata; the stream RW extent proves one canonical
allocation, and different emission windows must produce the same stream image.
Real input owners are opened before exercising the common-layout scan and
cancellation paths. The matching manual remains explicitly authored/UNRUN.

Working/staged environment-facade guards passed; the manual tree contains zero
executable `_spec.spl` files. Source review and fixture assembly do not replace
any pending Simple execution or Phase 4 gate.

Final acceptance also reverses the common declaration order, requires the exact
common-storage error at a 12399-byte cap (one byte short of the 12400-byte plan),
and mutates a real common record to maximum unsigned size before checking
failure and destination preservation. Whitespace and numbered-artifact checks
passed before these focused test additions; their final diff is checked again
because the tested content changed. No unchanged runtime check was repeated.

Final source/test review found no P0/P1, including all focused follow-ups.
Eleven patches rebased unchanged onto release base
`d1624747dcb895faf990395796776e49066141a7` (all range-diff entries equal).
Required structural CI passed on PR https://github.com/ormastes/simple/pull/2436.
Test-tree delta PASS: 3151 inherited offenders, zero introduced. The exact list
is retained at `C:/dev/simple/.git/item4-stream-common-preexisting-offenders.txt`,
SHA256 `52ac058b29cffa22e435ff81da0cfb5de6db910b102fa51759866e24fd1d4678`.
This is unchanged from the preceding ELF source/operation slices. The full-tree
divergence guard remains FAIL; its scoped delta is PASS. No source-only result
closes the runtime, coverage, generated-manual, enforcement or Phase 4 gates.

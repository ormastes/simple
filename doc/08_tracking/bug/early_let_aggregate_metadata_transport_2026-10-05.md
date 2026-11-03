# Early Let repeats the staged aggregate metadata transport defect

Related: phase2_subsystem_helper_mir_failures_2026-10-05.
The ten focused e37658 attempts all failed compilation with producer 2b831559;
typed lexer receivers still reported CoreLexer methods, text byte_at and HashMap
get/insert failures. No test assertions executed. This is a source-proven
compiler defect candidate, not evidence that all eight diagnostics are fixed.

The discriminant-dispatched Let path read a HirType aggregate from
find_local_hir_type and passed it into remember_local_hir_type. The ordinary Let
arm already avoids this exact staged ABI corruption using scalar local IDs and
copy_local_hir_type_metadata, preserving type/isolation/resource metadata inside
its owning arrays. The early arm now uses the same existing copy operation.
No source annotation workaround, method-name guess, type guard relaxation or
runtime payload representation change is introduced.

Three compiled lowering regressions cover text and named receiver rebindings,
plus scalar rejection. The four-check authored native fixture covers UTF-8 byte
identity, named mutable receiver value semantics, nested-array length/content.
All native/compiled tests are UNRUN pending coordinated fixed-producer builds.
Old-producer fixture success alone would not qualify the rebuilt compiler path.

Memory/performance: one metadata copy per existing binding, no new global cache
or runtime allocations. Timing and peak RSS comparisons remain UNRUN; no speed
or memory improvement is claimed. Remaining receiver-resolution failures need
their own evidence after this minimal fix; the existing unresolved method path
also only recovers Enum owners from declared Named types when struct metadata
is missing, which remains under investigation rather than bundled speculatively.

**Revalidated 2026-11-02: still plausible because the report title (Early Let transports aggregate receiver metadata across staged ABI) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 status: fix-implemented-verification-pending
Fix is in source (early Let uses `copy_local_hir_type_metadata`, `mir_lowering_stmts.spl:1668,1998`). `test/01_unit/compiler/mir/early_let_receiver_metadata_spec.spl` re-run on the seed: 3/3 pass. Closure: stage3 build of the lexer/HashMap modules shows none of the eight diagnostics.

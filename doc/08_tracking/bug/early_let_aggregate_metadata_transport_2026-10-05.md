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

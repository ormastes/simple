# Old Windows Stage 2 misrepresents typed text-array diagnostic inputs

Status: OPEN; distinct from the repaired integer-key HIR diagnostic crash.

The immutable old pure Stage 2 executable SHA-256
`62b9104ec2ad4f8a1bb75d5923cc78b55b761cc9c3e8f84a8010a8d4d7f5c37c`
compiled an isolated extraction of the repaired cold-HIR error diagnostic and
its executable exited zero. However, four expected source strings printed as
numeric handles, and the present text-keyed HIR dictionary entry was not found.
Five completion markers therefore did not constitute five semantic passes.

A separate fixture declared explicit `text`, `[text]`, and
`Dict<text, ProbeHir>` locals. The same anomaly remained. Its fixture SHA-256 is
`e78e607a12797a8c97bc56c97669271537f335b4362e9ddba07b73ca6f48525a`.
Root cause within the old compiler's collection/text lowering is unresolved;
do not infer a particular boxing or ABI repair from the output alone.

The exact same typed fixture compiled with the explicitly authorized private
fixed Rust seed using native LLVM and Cranelift passed a strict 20-line oracle:
four source paths equal `/other/main.spl`, only the present-name case prints
that HIR path, the empty-source case emits no path diagnostic, and all five
retain the error branch's false return. The original production block compiled
with seed LLVM and crashed with exit 139 at missing-name, independently confirming
the separate dictionary-index diagnostic repair. Seed runs are bootstrap
diagnostics only and do not qualify the pure compiler or satisfy full tests.

Evidence is retained beneath
`C:/dev/simple-phase4-evidence/crash-authority-20261011-attempt2/diagnostic-regression-typed/`:
`fixed`, `seed-llvm-fixed`, `seed-cranelift-fixed`, `seed-llvm-original`.
Each repaired variant has `semantic-result.json`; compile/run logs and exact
production extraction hashes remain adjacent. The reusable packaged harness
requires explicit producer/runtime and a fresh isolated output directory.

Follow-up: reproduce against the newly produced pure compiler and isolate
text-array access, field type propagation and dictionary key identity using
the same strict string oracle. Preserve this old-producer failure until real
pure-native evidence resolves it; do not normalize numeric handles in tests.

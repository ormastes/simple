# Bounded HIR encoder traversal

The canonical bounded writer admits generated node entries with a work charge and a depth limit (128 by default). The existing three-argument constructor remains accepted; a fourth argument selects a nonnegative depth limit. Failure uses the existing bounds receipt and `writer_depth` reason. Every admitted entry leaves even when a private body returns early; failed entry does not leave.

Generated variable-length loops charge each iteration and return on poison. Composite argument evaluation and traversal boundaries reject poison before accessing the next child. Dictionary snapshots and typed ordering are accounted before allocation/sort, including conservative text comparison bytes. Text encoding refuses poison before scanning and refuses an exceeded output budget during its preflight scan. Existing scalar writer methods reject poison themselves.

Finite scalar tails may unwind after a failed child. The checked-in projection has 97 encoder bodies, the largest containing 1091 source lines; a conservative static ceiling is 1091 fixed body statements per admitted frame, plus one failed loop-admission check per enclosing loop. No further child entry or variable loop body is admitted after poison. This is a control-flow bound, not measured CPU/RSS evidence; depth counts generated codec nodes rather than language nesting. Default unbounded writers preserve their unbounded compatibility behavior and valid byte schema.

## Evidence and open gates

`test/01_unit/compiler/hir/hir_codec_writer_traversal_bounds_spec.spl` records exact wire equality, depth/unwind, broad-work exhaustion, poison, constructor compatibility, and key admission regressions. They have **not been executed** in this session. Static inspection confirms all 97 wrapper/body pairs, per-loop admission, unchanged decoder text and unchanged generated public exports.

The generated file was mechanically projected from the prior checked-in file using the source generator transformation. This is not execution of the Simple generator. Run `bin/simple run src/app/compiler_schema/main.spl codec` and `sh scripts/check/check-hir-codec-complete.shs` only with an admitted runtime, then execute the focused specs and adjacent canonical golden tests. Generation reproducibility, runtime wire equality, startup/request latency and max RSS remain pending. Canonical generated availability remains false. This patch addresses encoder traversal; it does not qualify the whole codec or bound callers that recursively traverse before invoking it.

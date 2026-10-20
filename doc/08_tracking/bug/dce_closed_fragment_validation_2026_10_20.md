# Closed MIR DCE had no actual artifact validation path

Status: source implementation authored; runtime/Lean UNRUN. Bug database
registration pending; no bug-add command was executed.

At d9e177, `dce_tv_validate` accepted caller-built model programs and recursively
rescanned suffixes. There was no actual MirFunction extractor/integration.
`DeadCodeElimination.is_instruction_result_used` always returned true after
its scan, conservatively preserving every Const/Add/Copy. Its span comparison
could not provide positional identity. The exported dce_run_on_function
wrapper also returned its input, and ordinary registry DCE remained inactive.

The scoped fix adds an explicit checked closed-fragment mode to the real class,
using unique validated SSA IDs and instruction indices, fresh snapshots and
candidate arrays, and linear one-pass liveness. Default conservative behavior
and the free-function wrapper remain unchanged. No general DCE activation is
claimed. The abstract validator is linearized without changing its relation;
old optimize/dead-query code remains byte-identical.

LLVM i64 Add uses `add nsw`, unlike the wrapping BitVec64 proof model. The
extractor admits only closed, exactly derived additions proved not to overflow
before evaluation. General overflow-language semantics remain unresolved by
this slice; backend behavior and theorem are not changed.

See `doc/05_design/dce_mir_translation_validation.md` and the two mirrored
actual-MIR/differential manuals for scope and remaining C7 obligations.

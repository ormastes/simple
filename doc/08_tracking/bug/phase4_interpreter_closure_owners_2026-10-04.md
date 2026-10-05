# Phase4 standalone interpreter closure owners

Status: AST import repair prepared; control/operator gaps remain open.

The Windows source9737/producer776ce2 standalone interpreter collected 97 files
then failed before HIR. ast_convert imports `interpreter.ast_types`,
`interpreter.ast_convert_stmt`, and `interpreter.ast_convert_expr`, although
their physical owner is `src/app/interpreter`. The four AST conversion modules
now consistently name `app.interpreter` for their sibling imports.

The same run also failed on `..control` from core/eval and `shared.operators`
from expr/arithmetic. The physical control package is nested at
`control/control/__init__.spl` and does not export the requested `eval_control`.
Existing compiler interpreter/semantic modules contain some operator names,
but their signatures and Value/error types are not automatically compatible.
Do not substitute imports or stub dispatch merely to pass source collection.

Required next evidence: collect the standalone interpreter closure with the
corrected source, repair real control/operator ownership, compile and execute
its --eval, script, and error-path tests. No native tests have run for this
change; the earlier failure is not a test-case failure or a successful build.

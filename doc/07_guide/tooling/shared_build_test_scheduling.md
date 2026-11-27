# Shared build and test scheduling

Status: candidate implementation; runtime qualification is pending.

Build tasks and ordinary parallel test files use
std.common.task_runner.execution_schedule for readiness, reservations, reap and
terminal transitions. The parent owns the ordinary host-count map. Children do
not mutate it, so a lockless map is unnecessary.

Dispatch reserves capacity before process creation. Reaping retains that charge;
the parent releases it only after domain acceptance or admitted retry. A denied
spawn can roll back only when no child was acquired. Unresolved descendant
cleanup retains capacity. Build wrappers retain their DAG, provenance, output
receipt and retry checks. Test wrappers retain process/RSS admission, deadlines,
bounded capture and deterministic input-order results.

Assert-ran interpreter children receive unique --test-result-file paths. The
child CLI configures its own evidence destination; the parent environment is
not changed. Canonical BDD receipts determine counts, and green human output
cannot replace missing evidence, zero examples or deadline failure. Receipt and
expectation files are removed after collection proves reaping. The canonical
parser removes valid trace sidecars and retains malformed trace diagnostics.
Native child-test protocol remains separate.

Qualification requires a GNU Phase2 compiler that actually compiles Hello and
runs its output, then builds the runner and full child CLI. A zero compiler
exit without an executable is failure. Run the focused scheduler/receipt specs
and real parallel-child system spec with exact binary identity pins. Authored
tests, linked executables and directory names alone do not prove readiness.

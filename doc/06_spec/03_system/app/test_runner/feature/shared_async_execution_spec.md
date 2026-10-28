# Shared async execution scenarios

Status: authored manual; execution and SPipe generation/review pending.
Executable: test/03_system/app/test_runner/feature/shared_async_execution_spec.spl.

Run with SIMPLE_BINARY and SIMPLE_TEST_BINARY pointing to the same qualified
full CLI built by the GNU Phase2 compiler. Missing or mismatched pins fail.

## Two green children

Pin the qualified descendant CLI. Run the slow and fast fixture files with two
workers and assert-ran enabled through the shared async process owner. Expect
two results in input order, each with one passed example, no failures and a
successful outcome. This checks real child execution; collection-only unit
tests cannot substitute for it.

## Red child with a green sibling

Run a deliberately failing assertion and a green fixture together. Expect one
failed example for the red child and one passed example for the sibling. The
parent must collect both and retain manifest order.

## Zero-example child with a green sibling

Run an empty spec beside the green fixture. Expect the empty child to fail
with no executed BDD examples or unavailable structured evidence. The green
sibling still reports its real pass. Human transcript markers cannot fabricate
executed examples.

These scenarios do not independently prove hard RSS enforcement, stubborn-child
cleanup or all build receipt recovery contracts. Those remain separate gates
in doc/03_plan/sys_test/test_build_shared_execution_schedule.md.

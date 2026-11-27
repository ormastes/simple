# Native framework wrapper specification

Source: `test/01_unit/lib/test_runner/native_framework_wrapper_spec.spl`.
Status: **NOT_RUN**,15 authored structural cases,0 executed. This is an authored
review manual; canonical SPipe generation remains pending a qualified runner.

| Case | Actual contract checked |
|---|---|
| Wildcard framework import | Import and method matcher remain; no rt_bdd or local expect substitute |
| Named/multiline imports | Import braces and framework submodule remain outside main |
| Hooks and nested closures | Existing before/after/context/it bodies remain intact |
| Local import scopes | Helper and sibling-local aliases remain inside their original scopes |
| Module declarations | Struct, public helper and multiline global stay above main |
| Multiline fixture text | Matcher-like text and main-like text remain string payload |
| Infix compatibility | Executable infix expectation becomes a real method call |
| Quoted matcher text | Canonical string byte ranges preserve Unicode/quoted hashes and trailing comments |
| Native result ownership | Real summary/count/exit calls follow bodies; zero count refuses |
| Skipped-only source | Skip call remains and cannot bypass zero-executed guard |
| Alias collision | Caller declaration remains; result import uses a distinct alias |
| Existing main | A second top-level entrypoint is refused |
| Method main | Class method is preserved without confusing it with the entrypoint |
| Invalid source mapping | Empty source and inconsistent facts fail before unsafe indexing |
| Legacy partition | Harness filtering/governance imports/list declarations retain old behavior |

Use the selected configuration through generic std.test_runner/std.spec imports.
Do not qualify this by selecting a NoGC directory or substituting an interpreter
or a smaller handwritten test engine.

Mandatory independent native admission controls:

- `test/fixtures/test_runner/native_framework/hooks_and_siblings_spec.spl`:
  expected3 executed,3 passed,0 failed, exit0; real before/after hooks and nested
  closure behavior and a real module-scope struct constructor/field are asserted.
- `test/fixtures/test_runner/native_framework/failure_continuation_spec.spl`:
  expected3 executed,2 passed,1 deliberate assertion failure, exit1. Later cases
  and failed-case after hooks must execute; an infrastructure error is not PASS.

Retain producer hash, effective configuration, native generated entry, framework
export owner, runtime ABI, native invocation, actual case/expectation counts,
stdout/stderr and bounded process-tree cleanup receipts. These fixtures are
authored controls, not evidence that any test has already passed.

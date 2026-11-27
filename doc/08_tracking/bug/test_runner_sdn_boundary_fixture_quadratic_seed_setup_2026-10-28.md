# SDN output boundary fixture: quadratic interpreter setup

Status: test setup fixed; interpreter repeated-array mutation performance remains open.

On release source `e9bbb1ffbbc`, the Phase 1 bootstrap seed at
`src/compiler_rust/target/bootstrap/simple` timed out running
`test/01_unit/lib/test_runner/test_runner_output_sdn_spec.spl`.
The full runner invocation was bounded at 45 seconds. A separate instrumented
`simple run` invocation passed the first six examples, then spent its 60-second
budget constructing two 65,537-element arrays with repeated `push` calls.
At approximately 16 seconds only 20,000 elements had been constructed.
The serializer had not yet been called for that example. The growing array
mutation behaves quadratically in this interpreter; this is distinct from
SDN serialization performance or a collection-budget correctness failure.

The fixture now constructs `[""; 65537]` and
`[SdoctestModifier.IgnoreOutput; 65537]` directly, with explicit length
assertions. Both one-over-limit rejection assertions are retained, including
zero-length artifact strings and text-free modifiers. No production limit,
output behavior, skip tag, or timeout is changed.

After the change, the full spec completed in 1.471 seconds wall time
(903 ms reported test duration): 10 declared, 10 executed, 10 passed,
0 failures, no drops. Command:

```sh
/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple test \
  test/01_unit/lib/test_runner/test_runner_output_sdn_spec.spl \
  --mode=interpreter --no-session-daemon --sequential --no-db --no-cache --assert-ran
```

Evidence for this local run: `/private/tmp/runner-output-sdn-after.log`.
The earlier direct probe log is `/private/tmp/runner-output-sdn-direct.log`.
The Phase 1 bootstrap check does not establish native Phase 2 behavior.

Follow-up: investigate interpreter array binding/mutation cloning under
repeated `push`, and preserve value/alias semantics while removing quadratic
copies. That compiler change is outside this focused test-fixture repair.

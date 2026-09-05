# Async MIR behavior (CreatePromise/Await/Yield lane)

> Exercises the real async execution machinery reachable from specs: the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async MIR behavior (CreatePromise/Await/Yield lane)

Exercises the real async execution machinery reachable from specs: the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/async/async_mir_interpreter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the real async execution machinery reachable from specs: the
generator protocol (CreatePromise/Yield lowering) driven end to end with
real state transitions, plus the interpreter/JIT agreement of the same
program run as a subprocess through `bin/simple run`.

## Scenarios

### Async MIR Instructions

#### CreatePromise yields the initial state immediately

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- create a promise-carrying generator and observe its first value
   - Expected: xs.len() equals `1`
   - Expected: xs[0] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create a promise-carrying generator and observe its first value")
# evidence(protocol_json): yielded values asserted below are the complete typed oracle
val xs = take(generator_from_step(7, fn(s): (s + 1, false)), 3)
expect(xs.len()).to_equal(1)  # oracle: initial state is yielded, continue=false stops the sequence
expect(xs[0]).to_equal(7)
```

</details>

#### Await passes the promise value through the step chain

- step a generator whose state is the awaited value
   - Expected: xs[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("step a generator whose state is the awaited value")
# evidence(protocol_json): yielded values asserted below are the complete typed oracle
val xs = take(generator_from_step(42, fn(s): (s, false)), 5)
expect(xs[0]).to_equal(42)  # oracle: the awaited value crosses the step boundary unchanged
```

</details>

#### Yield advances state across multiple steps

- collect successive yields from a range generator
   - Expected: xs.len() equals `3`
   - Expected: xs[0] equals `1`
   - Expected: xs[1] equals `2`
   - Expected: xs[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collect successive yields from a range generator")
# evidence(protocol_json): yielded values asserted below are the complete typed oracle
val xs = take(generate_range(1, 4), 3)
expect(xs.len()).to_equal(3)
expect(xs[0]).to_equal(1)
expect(xs[1]).to_equal(2)
expect(xs[2]).to_equal(3)  # oracle: each yield advances the state exactly once
```

</details>

#### spawn/send/receive: a step function can carry compound state

- drive a tuple-state generator and inspect the final carried value
   - Expected: f[3][0] equals `2`
   - Expected: f[3][1] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drive a tuple-state generator and inspect the final carried value")
# evidence(protocol_json): carried state asserted below is the complete typed oracle
val fib = generator_from_step([0, 1], fn(state):
    val next = [state[1], state[0] + state[1]]
    (next, true)
)
val f = take(fib, 4)
expect(f[3][0]).to_equal(2)  # oracle: 4th fibonacci pair is [2, 3]
expect(f[3][1]).to_equal(3)
```

</details>

#### unknown/empty continuation terminates the sequence

- collect from a generator that never continues
   - Expected: take(generate_range(5, 5), 10).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collect from a generator that never continues")
# evidence(protocol_json): length asserted below is the complete typed oracle
expect(take(generate_range(5, 5), 10).len()).to_equal(1)  # oracle: only the initial state is yielded
```

</details>

#### interpreter and JIT engines agree on the same async-stepped program

- run an identical arithmetic program under both engines and compare stdout
   - Expected: ok is true
   - Expected: interp.is_ok() and jit.is_ok() is true
   - Expected: a.stdout equals `b.stdout`
   - Expected: a.stdout contains `ENGINE_SUM=`
   - Expected: "${m2}" equals `__unreachable__`
   - Expected: "${m1}" equals `__unreachable__`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("run an identical arithmetic program under both engines and compare stdout")
# evidence(protocol_json): identical stdout asserted below is the complete typed oracle
val ok = write_file("/tmp/sspec_async_engine_agree.spl", "var total = 0\nfor i in [1, 2, 3, 4, 5]:\n    total = total + i\nprint(\"ENGINE_SUM=\" + total.to_string())\n")
expect(ok).to_equal(true)
val interp = run_process("env", ["SIMPLE_EXECUTION_MODE=interpreter", "bin/simple", "run", "/tmp/sspec_async_engine_agree.spl"])
val jit = run_process("env", ["SIMPLE_EXECUTION_MODE=jit", "bin/simple", "run", "/tmp/sspec_async_engine_agree.spl"])
expect(interp.is_ok() and jit.is_ok()).to_equal(true)
match interp:
    case Ok(a):
        match jit:
            case Ok(b):
                expect(a.stdout).to_equal(b.stdout)  # oracle: both engines must print byte-identical output
                expect(a.stdout.contains("ENGINE_SUM=")).to_equal(true)
            case Err(m2):
                expect("${m2}").to_equal("__unreachable__")
    case Err(m1):
        expect("${m1}").to_equal("__unreachable__")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f96a9fc9c351729b2481b36a8674d0f2e9ce5514d0673840355ce607f7772713`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f96a9fc9c351729b2481b36a8674d0f2e9ce5514d0673840355ce607f7772713`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f96a9fc9c351729b2481b36a8674d0f2e9ce5514d0673840355ce607f7772713`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/compiler/async/async_mir_interpreter_spec.spl
mirror: doc/06_spec/unit/compiler/async/async_mir_interpreter_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/async/async_mir_interpreter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/async/async_mir_interpreter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/async/async_mir_interpreter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->

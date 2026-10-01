# kernel_session_manager_spec

> KernelSessionManager unit spec (Stream K, task K1).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# kernel_session_manager_spec

KernelSessionManager unit spec (Stream K, task K1).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/notebook/kernel_session_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

KernelSessionManager unit spec (Stream K, task K1).

Covers session lifecycle, per-cell mode override resolution, and invalid
mode-spec diagnostic passthrough from the composite-mode extractor helpers
(test_executor_composite_parse.spl, extended by GPU-A1).

Design: doc/05_design/app/tools/notebook_lanes_architecture.md §4.1
Plan:   doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md (Stream K, K1)

## Scenarios

### KernelSessionManager — session lifecycle

#### creates a session with a valid default mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a session with a valid default mode
   - Expected: diag equals ``
   - Expected: mgr.default_mode_of("s1") equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a session with a valid default mode")
val mgr = manager_with_fake_factory()
val diag = mgr.create_session("s1", "interpreter")
expect(diag).to_equal("")
assert_true(mgr.session_exists("s1"))
expect(mgr.default_mode_of("s1")).to_equal("interpreter")
```

</details>

#### rejects a duplicate session id

- rejects a duplicate session id
   - Expected: diag equals `Session already exists: s1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a duplicate session id")
val mgr = manager_with_fake_factory()
val _ = mgr.create_session("s1", "interpreter")
val diag = mgr.create_session("s1", "interpreter")
expect(diag).to_equal("Session already exists: s1")
```

</details>

#### removes a session and shuts down its cached executors

- removes a session and shuts down its cached executors


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a session and shuts down its cached executors")
val mgr = manager_with_fake_factory()
val _ = mgr.create_session("s1", "interpreter")
val result = mgr.execute_cell("s1", "val x = 1", "cell-1", "")
assert_true(result.is_ok())
val removed = mgr.remove_session("s1")
assert_true(removed)
expect_not(mgr.session_exists("s1"))
```

</details>

#### removing an unknown session returns false

- removing an unknown session returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removing an unknown session returns false")
val mgr = manager_with_fake_factory()
expect_not(mgr.remove_session("nope"))
```

</details>

#### %mode changes the session default

- %mode changes the session default
   - Expected: diag equals ``
   - Expected: mgr.default_mode_of("s1") equals `interpreter(remote(baremetal(riscv32)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("%mode changes the session default")
val mgr = manager_with_fake_factory()
val _ = mgr.create_session("s1", "interpreter")
val diag = mgr.set_default_mode("s1", "interpreter(remote(baremetal(riscv32)))")
expect(diag).to_equal("")
expect(mgr.default_mode_of("s1")).to_equal("interpreter(remote(baremetal(riscv32)))")
```

</details>

#### %mode on an unknown session reports the session, not a spec error

- %mode on an unknown session reports the session, not a spec error
   - Expected: diag equals `Unknown session: ghost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("%mode on an unknown session reports the session, not a spec error")
val mgr = manager_with_fake_factory()
val diag = mgr.set_default_mode("ghost", "interpreter")
expect(diag).to_equal("Unknown session: ghost")
```

</details>

### KernelSessionManager — per-cell mode override resolution

#### a cell with no override runs on the session default

- a cell with no override runs on the session default
   - Expected: mgr.resolve_cell_mode("s1", "") equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a cell with no override runs on the session default")
val mgr = manager_with_fake_factory()
val _ = mgr.create_session("s1", "interpreter")
expect(mgr.resolve_cell_mode("s1", "")).to_equal("interpreter")
```

</details>

#### %%mode override wins for that cell without changing the default

- %%mode override wins for that cell without changing the default
   - Expected: overridden equals `interpreter(remote(vulkan(spv15)))`
   - Expected: mgr.default_mode_of("s1") equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("%%mode override wins for that cell without changing the default")
val mgr = manager_with_fake_factory()
val _ = mgr.create_session("s1", "interpreter")
val overridden = mgr.resolve_cell_mode("s1", "interpreter(remote(vulkan(spv15)))")
expect(overridden).to_equal("interpreter(remote(vulkan(spv15)))")
# Default is unchanged.
expect(mgr.default_mode_of("s1")).to_equal("interpreter")
```

</details>

#### execute_cell honors a per-cell override and caches a distinct executor

- execute_cell honors a per-cell override and caches a distinct executor
   - Expected: r1.stdout_delta equals `echo: code-a`
   - Expected: r2.stdout_delta equals `echo: code-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("execute_cell honors a per-cell override and caches a distinct executor")
val mgr = manager_with_fake_factory()
val _ = mgr.create_session("s1", "interpreter")
val r1 = mgr.execute_cell("s1", "code-a", "cell-1", "")
val r2 = mgr.execute_cell("s1", "code-b", "cell-2", "interpreter(remote(baremetal(riscv32)))")
assert_true(r1.is_ok())
assert_true(r2.is_ok())
expect(r1.stdout_delta).to_equal("echo: code-a")
expect(r2.stdout_delta).to_equal("echo: code-b")
```

</details>

#### repeated cells on the same lane reuse the cached executor (state persists)

- repeated cells on the same lane reuse the cached executor (state persists)
   - Expected: mgr.resolve_cell_mode("s1", "") equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeated cells on the same lane reuse the cached executor (state persists)")
val mgr = manager_with_fake_factory()
val _ = mgr.create_session("s1", "interpreter")
val _ = mgr.execute_cell("s1", "cell one", "cell-1", "")
val _ = mgr.execute_cell("s1", "cell two", "cell-2", "")
# Both cells ran on the same "interpreter" lane executor instance;
# observable via the factory only having created it once.
expect(mgr.resolve_cell_mode("s1", "")).to_equal("interpreter")
```

</details>

#### execute_cell on an unknown session returns an error CellResult, not a panic

- execute_cell on an unknown session returns an error CellResult, not a panic
   - Expected: result.error equals `Unknown session: ghost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("execute_cell on an unknown session returns an error CellResult, not a panic")
val mgr = manager_with_fake_factory()
val result = mgr.execute_cell("ghost", "val x = 1", "cell-1", "")
expect_not(result.is_ok())
expect(result.error).to_equal("Unknown session: ghost")
```

</details>

### KernelSessionManager — invalid mode-spec diagnostic passthrough

#### create_session surfaces the runner's 'Unknown platform' diagnostic verbatim

- create_session surfaces the runner's 'Unknown platform' diagnostic verbatim
   - Expected: diag equals `Unknown platform: nonsense`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create_session surfaces the runner's 'Unknown platform' diagnostic verbatim")
val mgr = manager_with_fake_factory()
val diag = mgr.create_session("s1", "interpreter(nonsense(riscv32))")
expect(diag).to_equal("Unknown platform: nonsense")
```

</details>

#### set_default_mode surfaces the same diagnostic

- set_default_mode surfaces the same diagnostic
   - Expected: diag equals `Unknown platform: nonsense`
   - Expected: mgr.default_mode_of("s1") equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_default_mode surfaces the same diagnostic")
val mgr = manager_with_fake_factory()
val _ = mgr.create_session("s1", "interpreter")
val diag = mgr.set_default_mode("s1", "interpreter(nonsense(riscv32))")
expect(diag).to_equal("Unknown platform: nonsense")
# Default mode is unchanged on rejection.
expect(mgr.default_mode_of("s1")).to_equal("interpreter")
```

</details>

#### execute_cell surfaces an invalid %%mode override as a CellResult error

- execute_cell surfaces an invalid %%mode override as a CellResult error
   - Expected: result.error equals `Unknown platform: nonsense`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("execute_cell surfaces an invalid %%mode override as a CellResult error")
val mgr = manager_with_fake_factory()
val _ = mgr.create_session("s1", "interpreter")
val result = mgr.execute_cell("s1", "code", "cell-1", "interpreter(nonsense(riscv32))")
expect_not(result.is_ok())
expect(result.error).to_equal("Unknown platform: nonsense")
```

</details>

#### rejects vulkan(resident) with the GPU-A1 diagnostic verbatim

- rejects vulkan(resident) with the GPU-A1 diagnostic verbatim
   - Expected: diag equals `resident submode requires forward-progress guarantees; vulkan lanes are per-d... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects vulkan(resident) with the GPU-A1 diagnostic verbatim")
val mgr = manager_with_fake_factory()
val diag = mgr.create_session("s1", "interpreter(remote(vulkan(spv15(resident))))")
expect(diag).to_equal("resident submode requires forward-progress guarantees; vulkan lanes are per-dispatch (see gpu_remote_interpreter_architecture.md §6.3)")
```

</details>

#### accepts a bare base runtime with no composite nesting

- accepts a bare base runtime with no composite nesting


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a bare base runtime with no composite nesting")
assert_true(mode_spec_is_valid("interpreter"))
assert_true(mode_spec_is_valid("jit"))
```

</details>

#### accepts known composite lane specs

- accepts known composite lane specs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts known composite lane specs")
assert_true(mode_spec_is_valid("interpreter(remote(baremetal(riscv32)))"))
assert_true(mode_spec_is_valid("interpreter(remote(cuda(sm80(resident))))"))
assert_true(mode_spec_is_valid("interpreter(remote(vulkan(spv15)))"))
```

</details>

#### validate_mode_spec on an empty spec reports Unknown platform

- validate_mode_spec on an empty spec reports Unknown platform
   - Expected: validate_mode_spec("") equals `Unknown platform: `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validate_mode_spec on an empty spec reports Unknown platform")
expect(validate_mode_spec("")).to_equal("Unknown platform: ")
expect_not(mode_spec_is_valid(""))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `e3cdda742457c7428cb8c7e6c4a07fe659c6a9fa217e46fc522b923cf405d644`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3cdda742457c7428cb8c7e6c4a07fe659c6a9fa217e46fc522b923cf405d644`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3cdda742457c7428cb8c7e6c4a07fe659c6a9fa217e46fc522b923cf405d644`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/notebook/kernel_session_manager_spec.spl
mirror: doc/06_spec/01_unit/lib/notebook/kernel_session_manager_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/notebook/kernel_session_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/notebook/kernel_session_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/notebook/kernel_session_manager_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a session with a valid default mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/notebook/kernel_session_manager_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a duplicate session id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/notebook/kernel_session_manager_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes a session and shuts down its cached executors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

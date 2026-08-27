# Contract spec: test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl` and a green Results line.

## Scenarios

### hosted timestamp provider ownership

#### records and subtracts the Windows progress reset epoch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records and subtracts the Windows progress reset epoch
   - Expected: source.split("g_progress_start_nanos = rt_time_now_nanos();").len() - 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records and subtracts the Windows progress reset epoch")
val source = rt_file_read_text("src/runtime/runtime_timestamp.c") ?? ""
expect(source).to_contain("static int64_t g_progress_start_nanos = 0;")
expect(source.split("g_progress_start_nanos = rt_time_now_nanos();").len() - 1).to_equal(2)
expect(source).to_contain("int64_t elapsed_nanos = rt_time_now_nanos() - g_progress_start_nanos;")
expect(source).to_contain("if (elapsed_nanos <= 0) return 0.0;")
expect(source).to_contain("return (double)elapsed_nanos / 1000000000.0;")
expect(source).to_not_contain("return (double)rt_time_now_nanos() / 1000000000.0;")
```

</details>

#### uses a floor-day remainder for negative sub-second timestamps

- uses a floor-day remainder for negative sub-second timestamps
   - Expected: rt_timestamp_get_hour(-1) equals `23`
   - Expected: rt_timestamp_get_minute(-1) equals `59`
   - Expected: rt_timestamp_get_second(-1) equals `59`
   - Expected: rt_timestamp_get_microsecond(-1) equals `999999`
   - Expected: rt_timestamp_get_hour(0) equals `0`
   - Expected: rt_timestamp_get_microsecond(1) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses a floor-day remainder for negative sub-second timestamps")
expect(rt_timestamp_get_hour(-1)).to_equal(23)
expect(rt_timestamp_get_minute(-1)).to_equal(59)
expect(rt_timestamp_get_second(-1)).to_equal(59)
expect(rt_timestamp_get_microsecond(-1)).to_equal(999999)
expect(rt_timestamp_get_hour(0)).to_equal(0)
expect(rt_timestamp_get_microsecond(1)).to_equal(1)
```

</details>

#### keeps the bootstrap SFFI timestamp owner floor-based

- keeps the bootstrap SFFI timestamp owner floor-based
   - Expected: compiler_gen.split("micros.div_euclid(86_400_000_000)").len() - 1 equals `3`
   - Expected: compiler_gen.split("micros.rem_euclid(86_400_000_000)").len() - 1 equals `3`
   - Expected: app_gen.split("micros.div_euclid(86_400_000_000)").len() - 1 equals `3`
   - Expected: app_gen.split("micros.rem_euclid(86_400_000_000)").len() - 1 equals `3`
   - Expected: app_time equals `lib_time`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the bootstrap SFFI timestamp owner floor-based")
val source = rt_file_read_text("src/app/sffi_gen.templates/bootstrap_sffi.txt") ?? ""
expect(source).to_contain("micros.div_euclid(86_400_000_000)")
expect(source).to_contain("micros.rem_euclid(86_400_000_000)")
expect(source).to_not_contain("let secs = micros / 1_000_000")
val compiler_gen = rt_file_read_text("src/compiler/90.tools/sffi_gen/specs/time_mod.spl") ?? ""
val app_gen = rt_file_read_text("src/app/ffi_gen.specs/time_mod.spl") ?? ""
expect(compiler_gen.split("micros.div_euclid(86_400_000_000)").len() - 1).to_equal(3)
expect(compiler_gen.split("micros.rem_euclid(86_400_000_000)").len() - 1).to_equal(3)
expect(app_gen.split("micros.div_euclid(86_400_000_000)").len() - 1).to_equal(3)
expect(app_gen.split("micros.rem_euclid(86_400_000_000)").len() - 1).to_equal(3)
expect(compiler_gen).to_not_contain("chrono::")        expect(app_gen).to_not_contain("chrono::")
val workspace_gen = rt_file_read_text("src/compiler/90.tools/sffi_gen/sffi_gen_workspace.spl") ?? ""
expect(workspace_gen).to_not_contain("chrono = ")
val app_time = rt_file_read_text("src/app/io/time_ops.spl") ?? ""
val lib_time = rt_file_read_text("src/lib/nogc_sync_mut/io/time_ops.spl") ?? ""
expect(app_time).to_equal(lib_time)
expect(app_time).to_contain("use common.time_utils.{timestamp_get_year")
expect(app_time).to_not_contain("val _ = micros")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `765dde446598aef88005d58b9db19f0c2aa06175dfc01ecf278e601acb169b6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `765dde446598aef88005d58b9db19f0c2aa06175dfc01ecf278e601acb169b6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `765dde446598aef88005d58b9db19f0c2aa06175dfc01ecf278e601acb169b6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records and subtracts the Windows progress reset epoch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a floor-day remainder for negative sub-second timestamps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the bootstrap SFFI timestamp owner floor-based' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

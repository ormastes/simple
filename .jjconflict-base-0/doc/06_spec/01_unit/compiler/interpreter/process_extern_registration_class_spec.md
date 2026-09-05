# Process-extern registration — similar-problem detection spec (defect CLASS)

> Generalises doc/08_tracking/bug/interpreter_sffi_missing_piped_process_externs_2026-07-29.md

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process-extern registration — similar-problem detection spec (defect CLASS)

Generalises doc/08_tracking/bug/interpreter_sffi_missing_piped_process_externs_2026-07-29.md

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/process_extern_registration_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Generalises doc/08_tracking/bug/interpreter_sffi_missing_piped_process_externs_2026-07-29.md

THE CLASS: a runtime function that exists in `src/runtime/runtime_process.c`
and is declared `extern fn` by shipping Simple code, but was never added to the
interpreter's extern dispatch table in
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`.

Nothing in the build links those two lists. The C side compiles, the `.spl`
declaration parses, the JIT/native lane resolves the symbol at link time — and
only the interpreter fails, at semantic analysis, with
`unknown extern function: <name>`. There is no signal until a user runs the
affected program interpreted.

Five names (the entire piped sub-family) were missing SIMULTANEOUSLY and were
discovered one at a time. A spec that covered only `rt_process_spawn_piped`
would have shipped the other four. This spec therefore asserts the WHOLE
`rt_process_*` surface resolves, so the next unregistered member fails here
rather than in production.

WHY A SUBPROCESS: an unregistered extern kills the entire file at semantic
analysis, so an in-body call yields a ZERO-EXAMPLE file — which reads as a
pass, not a failure. Only a subprocess can distinguish "resolved" from
"the file never ran".

## Scenarios

### every rt_process_* extern declared by shipping code resolves in the interpreter

#### rejects any unregistered member of the process extern family

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects any unregistered member of the process extern family
- Run the registration census probe under SIMPLE_EXECUTION_MODE=interpret
- A single unregistered name aborts the whole file and names itself here
- Non-vacuity: the probe must have reached and printed its first resolution


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects any unregistered member of the process extern family")
step("Run the registration census probe under SIMPLE_EXECUTION_MODE=interpret")
val out = run_class_probe()

step("A single unregistered name aborts the whole file and names itself here")
expect(out).to_not_contain("unknown extern function")

step("Non-vacuity: the probe must have reached and printed its first resolution")
expect(out).to_contain("RESOLVED rt_process_run ")
```

</details>

#### resolves the long-registered process externs (control arm)

- resolves the long-registered process externs (control arm)
- These were always registered — a red here means the probe itself broke, not the table


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves the long-registered process externs (control arm)")
step("These were always registered — a red here means the probe itself broke, not the table")
val out = run_class_probe()
expect(out).to_contain("RESOLVED rt_process_run_inherit")
expect(out).to_contain("RESOLVED rt_process_run_timeout")
expect(out).to_contain("RESOLVED rt_process_run_bounded")
expect(out).to_contain("RESOLVED rt_process_spawn_async")
expect(out).to_contain("RESOLVED rt_process_wait")
expect(out).to_contain("RESOLVED rt_process_kill")
expect(out).to_contain("RESOLVED rt_process_is_running")
```

</details>

#### resolves the piped sub-family that was entirely absent (regression arm)

- resolves the piped sub-family that was entirely absent (regression arm)
- All five were missing at once — assert all five, not just the one that was noticed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves the piped sub-family that was entirely absent (regression arm)")
step("All five were missing at once — assert all five, not just the one that was noticed")
val out = run_class_probe()
expect(out).to_contain("RESOLVED rt_process_spawn_piped")
expect(out).to_contain("RESOLVED rt_process_write_stdin")
expect(out).to_contain("RESOLVED rt_process_read_stdout")
expect(out).to_contain("RESOLVED rt_process_is_alive")
expect(out).to_contain("RESOLVED rt_process_close_piped")
```

</details>

#### reports a census verdict naming the expected surface size

- reports a census verdict naming the expected surface size
- The count is in the verdict so that silently shrinking the census is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a census verdict naming the expected surface size")
step("The count is in the verdict so that silently shrinking the census is visible")
val out = run_class_probe()
expect(out).to_contain("PROCESS EXTERN REGISTRATION PROBE: ALL 13 RESOLVED")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `268a73d271242f720ab8eeb6711ba1a193f6f5815ea63c247a5b7fa5e6719bc3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `268a73d271242f720ab8eeb6711ba1a193f6f5815ea63c247a5b7fa5e6719bc3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `268a73d271242f720ab8eeb6711ba1a193f6f5815ea63c247a5b7fa5e6719bc3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/process_extern_registration_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/process_extern_registration_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/process_extern_registration_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/process_extern_registration_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/process_extern_registration_class_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects any unregistered member of the process extern family' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/process_extern_registration_class_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the long-registered process externs (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/process_extern_registration_class_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the piped sub-family that was entirely absent (regression arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

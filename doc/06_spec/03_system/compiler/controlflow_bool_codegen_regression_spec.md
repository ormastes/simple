# Control-Flow / Bool Native-Codegen Regression

> This SSpec guards four native-codegen-only fixes (all correct in the interpreter before their fix, but wrong or crashing once compiled to a native binary) against silent regression:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Control-Flow / Bool Native-Codegen Regression

This SSpec guards four native-codegen-only fixes (all correct in the interpreter before their fix, but wrong or crashing once compiled to a native binary) against silent regression:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #controlflow-bool-native-codegen-regression |
| Category | Compiler / Backend / Native Codegen |
| Status | Regression |
| Research | doc/08_tracking/bug/flat_bridge_bool_bitcast_and_text_corruption_2026-07-11.md |
| Source | `test/03_system/compiler/controlflow_bool_codegen_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec guards four native-codegen-only fixes (all correct in the
interpreter before their fix, but wrong or crashing once compiled to a
native binary) against silent regression:

- **#151** — `i64`/`iN` -> `bool` narrowing on an if/elif/else tail-merge
  emitted an invalid `bitcast i64 to i1` (rejected by `llc`, or on backends
  that tolerate it, garbage truth values); the fix in
  `src/compiler/70.backend/backend/mir_to_llvm_helpers.spl` and
  `_MirToLlvm/asm_constraints_helpers.spl` selects `trunc` for iN->i1 casts.
- **#150** — string concat/`.len()` corruption, plus `Result<T, E>` and
  `Option<T>` (`Dict.get()`) short-circuiting via the `?` operator, were
  unreliable once compiled natively.
- **#143** — `for x in <non-array iterable>` used to lower through
  null-function-pointer stub calls that `call 0` and SIGSEGV natively; the
  fix (`src/compiler/50.mir/mir_lowering_stmts.spl`) fails loudly on truly
  unsupported iterables, while the still-supported paths (`Range`, and
  arrays such as `Dict.keys()`/`Dict.values()`) must keep working correctly
  rather than crashing.
- **#144** — `i64_local.to_string()` printed via `println` resolved to
  `MethodResolution.Unresolved` on the bootstrap-flat lowering path and
  silently dropped the digits instead of rendering the decimal value.

Since the interpreter already gets all of these right, this spec's teeth are
in `--mode=native` (and the native-build-and-run probe below it): it must
fail loudly if any of the four regress.

## Research

**Research:** doc/08_tracking/bug/flat_bridge_bool_bitcast_and_text_corruption_2026-07-11.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/compiler/controlflow_bool_codegen_regression_spec.spl --mode=native --clean
```

## Scenarios

### control-flow / bool native-codegen regression

#### keeps bool tail-merge, Result/Option ?-propagation, for-in, and i64.to_string() green under interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps bool tail-merge, Result/Option ?-propagation, for-in, and i64.to_string() green under interpreter
- Write the combined control-flow/bool probe
   - Expected: write_out equals ``
   - Expected: write_code equals `0`
- Interpreter run reaches ALL_OK (proves the logic itself, not the native backend, is correct)
   - Expected: interp_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps bool tail-merge, Result/Option ?-propagation, for-in, and i64.to_string() green under interpreter")
step("Write the combined control-flow/bool probe")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_out).to_equal("")
expect(write_code).to_equal(0)

step("Interpreter run reaches ALL_OK (proves the logic itself, not the native backend, is correct)")
val (interp_out, interp_code) = shell(SIMPLE_BIN + " run " + SOURCE_PATH)
expect(interp_code).to_equal(0)
expect(interp_out).to_contain("ALL_OK")
expect(interp_out).to_contain("n_to_string=12345")
```

</details>

#### keeps bool tail-merge, Result/Option ?-propagation, for-in, and i64.to_string() green under native codegen

- keeps bool tail-merge, Result/Option ?-propagation, for-in, and i64.to_string() green under native codegen
- Hosted native compile of the probe still succeeds
   - Expected: compile_code equals `0`
- The standalone native probe exits 0 and prints ALL_OK instead of crashing or returning a per-bug failure code
   - Expected: native_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps bool tail-merge, Result/Option ?-propagation, for-in, and i64.to_string() green under native codegen")
step("Hosted native compile of the probe still succeeds")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The standalone native probe exits 0 and prints ALL_OK instead of crashing or returning a per-bug failure code")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/controlflow_bool_probe.out 2>&1; code=$?; cat /tmp/controlflow_bool_probe.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("ALL_OK")
expect(native_out).to_contain("n_to_string=12345")
expect(native_out).to_contain("EXIT=0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/08_tracking/bug/flat_bridge_bool_bitcast_and_text_corruption_2026-07-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `426bfed2eda93481b8a201d9b45f315e7cfdf033a5100d17a64e856036d71a72`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `426bfed2eda93481b8a201d9b45f315e7cfdf033a5100d17a64e856036d71a72`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `426bfed2eda93481b8a201d9b45f315e7cfdf033a5100d17a64e856036d71a72`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/compiler/controlflow_bool_codegen_regression_spec.spl
mirror: doc/06_spec/03_system/compiler/controlflow_bool_codegen_regression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/controlflow_bool_codegen_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/controlflow_bool_codegen_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/controlflow_bool_codegen_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/controlflow_bool_codegen_regression_spec.spl:176:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps bool tail-merge, Result/Option ?-propagation, for-in, and i64.to_string() green under interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/controlflow_bool_codegen_regression_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps bool tail-merge, Result/Option ?-propagation, for-in, and i64.to_string() green under native codegen' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# native_build_arg_source_spec

> Purpose: this manual pins the behavior named "native-build CLI arg source regressions" for the owning engineering team.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_build_arg_source_spec

Purpose: this manual pins the behavior named "native-build CLI arg source regressions" for the owning engineering team.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/native_build_arg_source_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose: this manual pins the behavior named "native-build CLI arg source regressions" for the owning engineering team.
    Audience: engineers verifying regressions in this area; steps below are executable evidence.

## Scenarios

### native-build CLI arg source regressions

#### routes omitted --backend through the default Simple LLVM backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes omitted --backend through the default Simple LLVM backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes omitted --backend through the default Simple LLVM backend")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")
expect(source).to_contain("not saw_backend")
```

</details>

#### does not treat malformed --backend as omitted

- does not treat malformed --backend as omitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not treat malformed --backend as omitted")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")
expect(source).to_contain("fn native_build_backend_supported(backend: text) -> bool:")
expect(source).to_contain("if str_eq(arg, \"--backend\"):")
expect(source).to_contain("return native_build_backend_supported(args[i + 1])")
expect(source).to_contain("return false")
assert_false(source.contains("arg == \"--backend\""))
assert_false(source.contains("backend == \"llvm"))
```

</details>

#### matches native-build command exactly

- matches native-build command exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("matches native-build command exactly")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = file_read("src/app/cli/_CliMain/main_and_help.spl")
expect(source).to_contain("str_eq(args[0], \"native-build\")")
assert_false(source.contains("args[0].starts_with(\"native-build\")"))
```

</details>

#### keeps native_build_main option checks off raw string equality

- keeps native_build_main option checks off raw string equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps native_build_main option checks off raw string equality")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = file_read("src/app/cli/native_build_main.spl")
expect(source).to_contain("native_build_text_eq(raw_args[i], \"native-build\")")
expect(source).to_contain("native_build_text_eq(args[i], \"--timeout\")")
expect(source).to_contain("native_build_text_eq(a, \"-o\")")
expect(source).to_contain("native_build_text_eq(a, \"--output\")")
expect(source).to_contain("fn native_build_has_help(args: [text]) -> bool:")
assert_false(source.contains("raw_args[i] == \"native-build\""))
assert_false(source.contains("args[i] == \"--timeout\""))
assert_false(source.contains("a == \"-o\""))
assert_false(source.contains("args.contains(\"-h\")"))
```

</details>

#### matches only --entry and --entry=value for native-build entry parsing

- matches only --entry and --entry=value for native-build entry parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("matches only --entry and --entry=value for native-build entry parsing")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(source).to_contain("arg == \"--entry\" or arg.starts_with(\"--entry=\")")
assert_false(source.contains("elif a.starts_with(\"--entry\")"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8948d0e7d8e283bcac8692f1635051c013fecfd8aa71f3357fe85ae8e851c9ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8948d0e7d8e283bcac8692f1635051c013fecfd8aa71f3357fe85ae8e851c9ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8948d0e7d8e283bcac8692f1635051c013fecfd8aa71f3357fe85ae8e851c9ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/unit/app/cli/native_build_arg_source_spec.spl
mirror: doc/06_spec/unit/app/cli/native_build_arg_source_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/native_build_arg_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/native_build_arg_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

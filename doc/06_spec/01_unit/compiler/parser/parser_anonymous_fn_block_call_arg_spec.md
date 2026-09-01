# parser_anonymous_fn_block_call_arg_spec

> Regression coverage for parser_anonymous_fn_block_call_arg_2026-08-03.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parser_anonymous_fn_block_call_arg_spec

Regression coverage for parser_anonymous_fn_block_call_arg_2026-08-03.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/parser_anonymous_fn_block_call_arg_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression coverage for parser_anonymous_fn_block_call_arg_2026-08-03.

Anonymous `fn(...)` block lambdas inside call parentheses must retain their
own NEWLINE/INDENT/DEDENT stream, just like backslash block lambdas.

## Scenarios

### anonymous fn block call arguments

#### parses the api surface snapshot sort comparator exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the api surface snapshot sort comparator exactly
   - Expected: parses_clean("anonymous_fn_exact_sort.spl", exact_sort_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the api surface snapshot sort comparator exactly")
expect(parses_clean("anonymous_fn_exact_sort.spl", exact_sort_source())).to_equal(true)
```

</details>

#### ends the lambda at a comma and parses the adjacent call argument

- ends the lambda at a comma and parses the adjacent call argument
   - Expected: parses_clean("anonymous_fn_comma_terminator.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends the lambda at a comma and parses the adjacent call argument")
val source = "fn apply() -> i64:\n" +
    "    val result = choose(fn(x: i64) -> i64:\n" +
    "        val doubled = x * 2\n" +
    "        doubled + 1\n" +
    "    , 7)\n" +
    "    result\n"
expect(parses_clean("anonymous_fn_comma_terminator.spl", source)).to_equal(true)
```

</details>

#### keeps expression-bodied anonymous fn syntax unchanged

- keeps expression-bodied anonymous fn syntax unchanged
   - Expected: parses_clean("anonymous_fn_expression_body.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps expression-bodied anonymous fn syntax unchanged")
val source = "fn apply() -> i64:\n" +
    "    val callback = fn(x: i64) -> i64: x + 1\n" +
    "    callback(2)\n"
expect(parses_clean("anonymous_fn_expression_body.spl", source)).to_equal(true)
```

</details>

#### parses the Stage 4 BackendPort expression callbacks exactly

- parses the Stage 4 BackendPort expression callbacks exactly
   - Expected: parses_clean("anonymous_fn_backend_port_exact.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the Stage 4 BackendPort expression callbacks exactly")
val source = "fn backend_port(interp_name: text):\n" +
    "    val backend = BackendPort(\n" +
    "        name: interp_name,\n" +
    "        run_fn: fn(m): interp_impl.process_module(m),\n" +
    "        supports_jit_fn: fn(): false,\n" +
    "        target_triple_fn: fn(): interp_name\n" +
    "    )\n" +
    "    backend\n"
expect(parses_clean("anonymous_fn_backend_port_exact.spl", source)).to_equal(true)
```

</details>

#### accepts a newline before the comma to an adjacent call argument

- accepts a newline before the comma to an adjacent call argument
   - Expected: parses_clean("anonymous_fn_adjacent_argument.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a newline before the comma to an adjacent call argument")
val source = "fn configure_callback():\n" +
    "    val configured = configure(\n" +
    "        callback: fn(): false\n" +
    "        , label: \"next\"\n" +
    "    )\n" +
    "    configured\n"
expect(parses_clean("anonymous_fn_adjacent_argument.spl", source)).to_equal(true)
```

</details>

#### reports a malformed block then clears parser error state for a valid parse

- reports a malformed block then clears parser error state for a valid parse
   - Expected: parses_clean("anonymous_fn_malformed.spl", malformed) is false
   - Expected: parses_clean("anonymous_fn_recovery.spl", exact_sort_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a malformed block then clears parser error state for a valid parse")
val malformed = "fn broken() -> i64:\n" +
    "    val callback = consume(fn(x: i64) -> i64:\n" +
    "        val missing =\n" +
    "    )\n" +
    "    callback\n"
expect(parses_clean("anonymous_fn_malformed.spl", malformed)).to_equal(false)
expect(parses_clean("anonymous_fn_recovery.spl", exact_sort_source())).to_equal(true)
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

- Canonical SPipe generation for source `ea943c6dbb658f4d5a21b689be761bc29346134febb0a7b58428ff7e41f4b343`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea943c6dbb658f4d5a21b689be761bc29346134febb0a7b58428ff7e41f4b343`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea943c6dbb658f4d5a21b689be761bc29346134febb0a7b58428ff7e41f4b343`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/parser_anonymous_fn_block_call_arg_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/parser_anonymous_fn_block_call_arg_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/parser_anonymous_fn_block_call_arg_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/parser_anonymous_fn_block_call_arg_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/parser_anonymous_fn_block_call_arg_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the api surface snapshot sort comparator exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/parser_anonymous_fn_block_call_arg_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ends the lambda at a comma and parses the adjacent call argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/parser_anonymous_fn_block_call_arg_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps expression-bodied anonymous fn syntax unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# parser_actor_spec

> Purpose and audience: compiler engineers on the parser team who need actor

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parser_actor_spec

Purpose and audience: compiler engineers on the parser team who need actor

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/parser_actor_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: compiler engineers on the parser team who need actor
    declarations — plain, public, documented, empty, method-bearing, and
    alongside classes — to parse into runnable programs, and malformed actor
    headers to be rejected with a parse error.

## Scenarios

### Parser actor definitions

#### a simple actor with one field parses and spawns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compile and run a fixture with a one-field actor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture with a one-field actor")
val out = compile_source("simple", SIMPLE_ACTOR)
expect(out).to_contain("simple ok")
```

</details>

#### an actor with multiple methods parses

- compile and run a fixture whose actor declares two methods
- methods exist on the parsed actor; invocation after spawn is
- not executable on the deployed seed (see limitation note)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture whose actor declares two methods")
val out = compile_source("methods", METHODS_ACTOR)
step("methods exist on the parsed actor; invocation after spawn is")
step("not executable on the deployed seed (see limitation note)")
expect(out).to_contain("methods ok")
```

</details>

#### an actor method with parameters and a return type parses

- compile and run a fixture with fn process(self, task: i64) -> i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture with fn process(self, task: i64) -> i64")
val out = compile_source("params", PARAMS_ACTOR)
expect(out).to_contain("params ok")
```

</details>

#### a pub actor keeps its visibility through parsing

- compile and run a fixture with a pub actor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture with a pub actor")
val out = compile_source("pub", PUB_ACTOR)
expect(out).to_contain("pub ok")
```

</details>

#### an actor with a doc comment parses

- compile and run a fixture with a documented actor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture with a documented actor")
val out = compile_source("doc", DOC_ACTOR)
expect(out).to_contain("doc ok")
```

</details>

#### an empty actor body parses

- compile and run a fixture whose actor body is a bare pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture whose actor body is a bare pass")
val out = compile_source("empty", EMPTY_ACTOR)
expect(out).to_contain("empty ok")
```

</details>

#### several actors in one file each parse and spawn

- compile and run a fixture declaring two actors


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture declaring two actors")
val out = compile_source("two", TWO_ACTORS)
expect(out).to_contain("two actors ok")
```

</details>

#### actors and classes coexist in one file

- compile and run a fixture with a class and an actor
- the class method stays callable while the actor spawns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture with a class and an actor")
val out = compile_source("mixed", ACTOR_AND_CLASS)
step("the class method stays callable while the actor spawns")
expect(out).to_contain("class and actor")
```

</details>

#### an actor header missing its colon is rejected with a parse error

- compile a fixture whose actor header lacks the colon
- the parser refuses the file instead of running it


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile a fixture whose actor header lacks the colon")
val out = compile_source("missing_colon", MISSING_COLON_ACTOR)
step("the parser refuses the file instead of running it")
expect(out).to_contain("parse:")
expect(out).to_contain("expected Colon")
expect(out).to_contain("compile failed")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `b31a5ba003e13bda8b150a6b2e5b27bce79fddcb912d6243cdd878b37e5c76ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b31a5ba003e13bda8b150a6b2e5b27bce79fddcb912d6243cdd878b37e5c76ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b31a5ba003e13bda8b150a6b2e5b27bce79fddcb912d6243cdd878b37e5c76ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/parser_actor_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/parser_actor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/parser_actor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/parser_actor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/parser_actor_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a simple actor with one field parses and spawns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/parser_actor_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an actor with multiple methods parses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/parser_actor_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an actor method with parameters and a return type parses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

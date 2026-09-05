# struct_literal_not_routed_to_static_new_spec

> Struct literal construction must not be auto-routed to a static `new`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# struct_literal_not_routed_to_static_new_spec

Struct literal construction must not be auto-routed to a static `new`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/interpreter/struct_literal_not_routed_to_static_new_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Struct literal construction must not be auto-routed to a static `new`.

Repro for doc/08_tracking/bug/enum_field_in_nested_call_arg_join_not_found_2026-08-17.md:
a fully-named struct literal whose field names coincide with an impl-static
`new`'s param NAMES (but not its param TYPES) was dispatched to `new`,
misbinding the args and surfacing spurious errors from inside `new`
(seen as "method 'join' not found on value of type enum in nested call
context"). `Point(x: 3, y: 4)` named-literal form is the canonical
constructor and must build the struct directly.

NOTE: fix landed 2026-08-17 in
src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs;
this spec goes green once the seed is redeployed.

## Scenarios

### struct literal vs static new routing

#### builds a fully-named struct literal directly, in statement position

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds a fully-named struct literal directly, in statement position
   - Expected: e.tags equals `pre`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a fully-named struct literal directly, in statement position")
val e = SlnEntry(name: "x", tags: "pre", color: SlnColor.Red)
expect(e.tags).to_equal("pre")
```

</details>

#### builds a fully-named struct literal directly, in nested call-arg position

- builds a fully-named struct literal directly, in nested call-arg position
   - Expected: sln_take(SlnEntry(name: "x", tags: "pre", color: SlnColor.Blue)) equals `pre`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a fully-named struct literal directly, in nested call-arg position")
expect(sln_take(SlnEntry(name: "x", tags: "pre", color: SlnColor.Blue))).to_equal("pre")
```

</details>

#### still routes an array-typed named call through the static new

- still routes an array-typed named call through the static new
   - Expected: e.tags equals `a,b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still routes an array-typed named call through the static new")
val e = SlnEntry.new(name: "y", tags: ["a", "b"], color: SlnColor.Red)
expect(e.tags).to_equal("a,b")
```

</details>

### constructor routing generalization

#### keeps auto-calling a non-static Python-style new

- keeps auto-calling a non-static Python-style new
   - Expected: c.label equals `hi!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps auto-calling a non-static Python-style new")
val c = SlnPyCtor(label: "hi")
expect(c.label).to_equal("hi!")
```

</details>

#### builds a plain struct with no new at all, nested in a call arg

- builds a plain struct with no new at all, nested in a call arg
   - Expected: sln_sum(SlnPlain(a: 2, b: 3)) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a plain struct with no new at all, nested in a call arg")
fn sln_sum(p: SlnPlain) -> i64:
    p.a + p.b
expect(sln_sum(SlnPlain(a: 2, b: 3))).to_equal(5)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c73c4f34ed80cc985929e7badd10e5b3f58bd9fa7ea4343ef87e21d1810f0c13`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c73c4f34ed80cc985929e7badd10e5b3f58bd9fa7ea4343ef87e21d1810f0c13`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c73c4f34ed80cc985929e7badd10e5b3f58bd9fa7ea4343ef87e21d1810f0c13`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/interpreter/struct_literal_not_routed_to_static_new_spec.spl
mirror: doc/06_spec/unit/compiler/interpreter/struct_literal_not_routed_to_static_new_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/interpreter/struct_literal_not_routed_to_static_new_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/interpreter/struct_literal_not_routed_to_static_new_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/interpreter/struct_literal_not_routed_to_static_new_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/interpreter/struct_literal_not_routed_to_static_new_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a fully-named struct literal directly, in statement position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/struct_literal_not_routed_to_static_new_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a fully-named struct literal directly, in nested call-arg position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/struct_literal_not_routed_to_static_new_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still routes an array-typed named call through the static new' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

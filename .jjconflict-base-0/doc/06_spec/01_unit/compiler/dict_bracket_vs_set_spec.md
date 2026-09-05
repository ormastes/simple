# Dict bracket-assign vs .set() write/read parity

> `d[k] = v` (bracket-assign) and `d.set(k, v)` (method-call write) must both persist the insert and must both be readable back through `d[k]`, `d.get(k)`, and `d.contains_key(k)`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict bracket-assign vs .set() write/read parity

`d[k] = v` (bracket-assign) and `d.set(k, v)` (method-call write) must both persist the insert and must both be readable back through `d[k]`, `d.get(k)`, and `d.contains_key(k)`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MIR-DICT-SET-WRITE |
| Category | Compiler / MIR lowering |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/08_tracking/bug/builtin_dict_set_silent_insert_audit_2026-07-31.md, |
| Source | `test/01_unit/compiler/dict_bracket_vs_set_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`d[k] = v` (bracket-assign) and `d.set(k, v)` (method-call write) must both
persist the insert and must both be readable back through `d[k]`,
`d.get(k)`, and `d.contains_key(k)`.

## Lane coverage warning -- READ BEFORE TRUSTING A GREEN RUN

`bin/simple test` runs on `bin/simple`, which is the **Rust bootstrap seed**
(`WARNING: this Rust-built Simple binary is a bootstrap seed only`), not the
self-hosted compiler -- confirmed via `src/compiler_rust/driver/src/seed_warning.rs`
and Rust `tracing`-style log formatting. The original filing this spec guards
against (`.set()` broken under native codegen) explicitly says the seed was
**never** the affected lane -- so a green run here, on either the seed's
interpreter (`bin/simple test`) or its Cranelift JIT (`bin/simple run`), is
**not evidence for or against the real defect**.

**The real self-hosted/native-codegen lane (`bootstrap/stage3/.../simple
compile`/`native-build`) currently shows a genuine, different-shaped defect:
`.set(` on a builtin `Dict` fails MIR lowering with `unresolved method call:
set`, while `d[k]=v` lowers cleanly.** That lane also segfaults on trivial
Dict-free hello-world programs (a separate, already-tracked, pre-existing
defect, not fixed or re-filed here), so a full read-back parity table could
not be produced there. Full transcript, the seed-lane table (included only
for completeness, not as proof), and the self-hosted MIR error:
`doc/08_tracking/bug/dict_set_bracket_write_parity_2026-08-07.md`.

**Do not treat this spec's green `Results:` line as proof `.set()` is safe.**
It only proves the seed's interpreter accepts and round-trips these calls
(which was never in question) -- keep steering call sites to `d[k]=v`.
`d[k]=v` lowers as an Index-assign, a different MIR construct than a method
call, so it never hits the missing dispatch arm below; `.set(` is confirmed
absent from the builtin-Dict method whitelist at
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1196`
(`is_dict_method_name`), which is why it fails MIR lowering with
`unresolved method call: set` on the real lane.

## Scenarios

### Dict bracket-assign vs .set() write parity

#### both write methods insert a readable i64 value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- both write methods insert a readable i64 value
   - Expected: d["a"] equals `1`
   - Expected: d.get("a") equals `1`
   - Expected: d["b"] equals `2`
   - Expected: d.get("b") equals `2`
   - Expected: d.contains_key("a") is true
   - Expected: d.contains_key("b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("both write methods insert a readable i64 value")
var d: Dict<text, i64> = {}
d["a"] = 1
d.set("b", 2)

expect(d["a"]).to_equal(1)
expect(d.get("a")).to_equal(1)
expect(d["b"]).to_equal(2)
expect(d.get("b")).to_equal(2)
expect(d.contains_key("a")).to_equal(true)
expect(d.contains_key("b")).to_equal(true)
```

</details>

#### both write methods insert a readable text value

- both write methods insert a readable text value
   - Expected: d["a"] equals `one`
   - Expected: d.get("a") equals `one`
   - Expected: d["b"] equals `two`
   - Expected: d.get("b") equals `two`
   - Expected: d.contains_key("a") is true
   - Expected: d.contains_key("b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("both write methods insert a readable text value")
var d: Dict<text, text> = {}
d["a"] = "one"
d.set("b", "two")

expect(d["a"]).to_equal("one")
expect(d.get("a")).to_equal("one")
expect(d["b"]).to_equal("two")
expect(d.get("b")).to_equal("two")
expect(d.contains_key("a")).to_equal(true)
expect(d.contains_key("b")).to_equal(true)
```

</details>

#### counts both writes in len()/keys()

- counts both writes in len()/keys()
   - Expected: d.keys().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts both writes in len()/keys()")
var d: Dict<text, i64> = {}
d["a"] = 1
d.set("b", 2)
expect(d.keys().len()).to_equal(2)
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


## Related Documentation

- **Research:** `doc/08_tracking/bug/builtin_dict_set_silent_insert_audit_2026-07-31.md,`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ac0c3eb2e38458362333268717269eb7b78353aa910536feb088c83e75c5ef0e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac0c3eb2e38458362333268717269eb7b78353aa910536feb088c83e75c5ef0e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac0c3eb2e38458362333268717269eb7b78353aa910536feb088c83e75c5ef0e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/dict_bracket_vs_set_spec.spl
mirror: doc/06_spec/01_unit/compiler/dict_bracket_vs_set_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/dict_bracket_vs_set_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/dict_bracket_vs_set_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/dict_bracket_vs_set_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/dict_bracket_vs_set_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'both write methods insert a readable i64 value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dict_bracket_vs_set_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'both write methods insert a readable text value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dict_bracket_vs_set_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts both writes in len()/keys()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

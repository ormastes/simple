# An import of a module that does not exist must not compile

> Six stdlib files shipped `use string.{char_from_code}`. The module path `string`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# An import of a module that does not exist must not compile

Six stdlib files shipped `use string.{char_from_code}`. The module path `string`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Implemented |
| Source | `test/02_integration/compiler/unresolved_import_is_hard_error_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Six stdlib files shipped `use string.{char_from_code}`. The module path `string`
has never existed anywhere in this tree. The Rust seed reported it only as
`[WARN] Failed to load imported types`, the JIT fallback then swallowed the
lowering failure and dropped the module to the interpreter, and the files
compiled clean. Every call died at RUNTIME with `semantic: function
char_from_code not found` -- a diagnostic that never mentions the import that
caused it -- leaving DNS label/TXT rdata decoding and SMTP base64 and
quoted-printable broken in shipped code.

One warning-level diagnostic let six broken files through. This spec pins the
two mechanisms that now stop it.

## Scope and Preconditions

Two independent guards, checked separately here because they fail at different
times and neither subsumes the other:

1. **Compile-time (the fix).** `1478ca64460` makes the resolver's E1034
   `cannot resolve import` a `LowerError::UnresolvedImport`, and escalates it
   unconditionally past the JIT interpreter fallback. This only takes effect in
   a binary built after that commit.
2. **Source-level (the gate).** `check-no-phantom-module-imports.shs` resolves
   every bare single-segment `use` in `src/**` against the tree with no
   compiler involved, and fails closed on any import root that resolves
   nowhere. It gates the source regardless of which binary is deployed.

## Key Concepts

| Concept | Description |
|---------|-------------|
| phantom module import | a `use` whose module path exists nowhere on the resolution path |
| baseline | the 22 findings that predate the gate; the gate fails on anything NOT in it |

## Recovery and Troubleshooting

A FAIL naming a new phantom means the import is a typo or names a module that
was never written. Fix the import or add the module. `SIMPLE_ALLOW_UNRESOLVED_IMPORTS=1`
restores the compiler's old warn-and-continue behaviour and exists only as a
break-glass for bisecting an unrelated failure.

## Compatibility and Limitations

The gate covers bare single-segment import roots -- the exact shape of the
incident, and the only shape resolvable without reimplementing the module
resolver. Dotted paths (`use std.x.y`) are left to the compiler's own resolver.
The separate class of a RESOLVED module that does not provide a NAMED item is
still only a `[use-warning]`; 16 distinct instances exist in the loaded stdlib
closure today, so it could not be escalated in the same change.

## Scenarios

### Phantom module imports are gated at the source level

#### reports no new phantom import in the tree

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports no new phantom import in the tree
   - Expected: status equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports no new phantom import in the tree")
# step: "Run the phantom-import gate over src/"
val (out, err, status) = rt_process_run("sh", [
    "scripts/check/check-no-phantom-module-imports.shs"
])
# step: "The gate passes and says how many imports it actually checked"
expect(status).to_equal(0)
expect(out).to_contain("0 new phantom")
expect(out).to_contain("import(s) checked")
```

</details>

#### never reports a vacuous pass

- never reports a vacuous pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("never reports a vacuous pass")
# step: "Read the count the gate claims to have checked"
val (out, err, status) = rt_process_run("sh", [
    "-c",
    "sh scripts/check/check-no-phantom-module-imports.shs | tail -1"
])
# step: "A run that examined zero imports must be an ERROR, never a PASS"
expect(out).to_not_contain("0 import(s) checked")
expect(out).to_not_contain("ERROR")
```

</details>

### Phantom module imports are rejected when introduced

#### fails closed on a newly introduced phantom import

- fails closed on a newly introduced phantom import
   - Expected: status equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails closed on a newly introduced phantom import")
# step: "Run the gate's own selftest, which injects a phantom import,
#        asserts the gate FAILS and names it, removes the file, and
#        asserts the tree returns to PASS"
val (out, err, status) = rt_process_run("sh", [
    "scripts/check/check-no-phantom-module-imports.shs",
    "--selftest"
])
# step: "Both fixtures pass, so a later PASS is evidence and not a
#        gate that cannot fail"
expect(status).to_equal(0)
expect(out).to_contain("selftest: 2 fixture(s) passed")
expect(out).to_not_contain("selftest fixture")
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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9e3ef51ab8b9b10c51cb5b130723f1cf900532b83f44d1644c27fc4eb5208238`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e3ef51ab8b9b10c51cb5b130723f1cf900532b83f44d1644c27fc4eb5208238`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e3ef51ab8b9b10c51cb5b130723f1cf900532b83f44d1644c27fc4eb5208238`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/compiler/unresolved_import_is_hard_error_spec.spl
mirror: doc/06_spec/02_integration/compiler/unresolved_import_is_hard_error_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/unresolved_import_is_hard_error_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/unresolved_import_is_hard_error_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/compiler/unresolved_import_is_hard_error_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/compiler/unresolved_import_is_hard_error_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no new phantom import in the tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/unresolved_import_is_hard_error_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never reports a vacuous pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/unresolved_import_is_hard_error_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on a newly introduced phantom import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

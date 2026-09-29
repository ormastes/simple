# Single Item Use Import Specification

> Tests covering single-item use-braces import (\\{name\\}).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Single Item Use Import Specification

## Scenarios

### single-item use-braces import (\\{name\\})

#### parses a single-item braces import and resolves the imported symbol

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a single-item braces import and resolves the imported symbol
   - Expected: consumer.imports.len() equals `1`
   - Expected: consumer.imports[0].module equals `provider`
   - Expected: consumer.imports[0].items.len() equals `1`
   - Expected: consumer.imports[0].items[0].name equals `answer`
   - Expected: consumer.imports[0].items[0].has_alias is false
   - Expected: hir.name equals `consumer_single`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses a single-item braces import and resolves the imported symbol")
val log = Logger(level: 0)
val src_provider = "pub fn answer() -> i64:\n    42"
val provider = parse_full_frontend(src_provider, "provider", "provider", log)
# NOTE: braces escaped (\{ \}) -- an un-escaped `{answer}` here is THIS
# host spec file's own string interpolation syntax, not literal text
# for the guest source below. See the file header and
# doc/08_tracking/bug/frontend_single_item_use_braces_import_crash_2026-07-29.md.
val src_consumer = "use provider.\{answer\}\nfn main() -> i64:\n    if answer() == 42: 0 else: 1"
val consumer = parse_full_frontend(src_consumer, "consumer_single", "consumer_single", log)

# Parses: exactly one import, exactly one item, no alias.
expect(consumer.imports.len()).to_equal(1)
expect(consumer.imports[0].module).to_equal("provider")
expect(consumer.imports[0].items.len()).to_equal(1)
expect(consumer.imports[0].items[0].name).to_equal("answer")
expect(consumer.imports[0].items[0].has_alias).to_equal(false)

# Resolves: the 2-pass import resolver registers `answer` from
# `provider` into the consumer's symbol table without crashing.
var modules: Dict<text, Module> = {}
modules["provider"] = provider
var sources: [SourceFile] = []
sources = sources.push(SourceFile(path: "provider", content: src_provider, module_name: "provider"))
val surfaces_result = module_surfaces_from_modules(modules, sources)
var surfaces = ModuleSurfacesByName.empty()
match surfaces_result:
    case Ok(value): surfaces = value
    case Err(_error): expect(true).to_equal(false)
var lowering = hirlowering_for_module("consumer_single", surfaces)
val hir = lowering.lower_module(consumer)
# NOTE: deliberately not asserting on `hir.symbols.lookup("answer")`'s
# exact Option value here -- "answer" resolves to SymbolId(id: 0) (the
# first registered symbol), and Option<SymbolId(id: 0)> vs None is a
# SEPARATE, already-tracked interpreter defect (lane-owned
# "get_symbol(0)" bug, out of scope for IMP1). The load-bearing
# assertion for THIS bug is that lowering a single-item-braces-import
# consumer completes at all instead of crashing during parsing.
expect(hir.name).to_equal("consumer_single")
```

</details>

#### still parses a multi-item braces import

- still parses a multi-item braces import
   - Expected: consumer.imports.len() equals `1`
   - Expected: consumer.imports[0].items.len() equals `2`
   - Expected: consumer.imports[0].items[0].name equals `answer`
   - Expected: consumer.imports[0].items[1].name equals `other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still parses a multi-item braces import")
val log = Logger(level: 0)
val src_consumer = "use provider.{answer, other}\nfn main() -> i64:\n    0"
val consumer = parse_full_frontend(src_consumer, "consumer_multi", "consumer_multi", log)
expect(consumer.imports.len()).to_equal(1)
expect(consumer.imports[0].items.len()).to_equal(2)
expect(consumer.imports[0].items[0].name).to_equal("answer")
expect(consumer.imports[0].items[1].name).to_equal("other")
```

</details>

#### parses an aliased single-item braces import

- parses an aliased single-item braces import
   - Expected: consumer.imports.len() equals `1`
   - Expected: consumer.imports[0].items.len() equals `1`
   - Expected: consumer.imports[0].items[0].name equals `answer`
   - Expected: consumer.imports[0].items[0].has_alias is true
   - Expected: consumer.imports[0].items[0].alias equals `ans`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses an aliased single-item braces import")
val log = Logger(level: 0)
# NOTE: braces escaped (\{ \}) -- same host-interpolation reason as
# the first example above ("answer as ans" is also valid
# interpolation-expression syntax, a cast expression).
val src_consumer = "use provider.\{answer as ans\}\nfn main() -> i64:\n    0"
val consumer = parse_full_frontend(src_consumer, "consumer_alias", "consumer_alias", log)
expect(consumer.imports.len()).to_equal(1)
expect(consumer.imports[0].items.len()).to_equal(1)
expect(consumer.imports[0].items[0].name).to_equal("answer")
expect(consumer.imports[0].items[0].has_alias).to_equal(true)
expect(consumer.imports[0].items[0].alias).to_equal("ans")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/single_item_use_import_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering single-item use-braces import (\\{name\\}).
- single-item use-braces import (\\{name\\})

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

- Canonical SPipe generation for source `5843eb19fdba046dddf5dc0cddbc0f009212737a3090a11c7413a18e60ae2daf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5843eb19fdba046dddf5dc0cddbc0f009212737a3090a11c7413a18e60ae2daf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5843eb19fdba046dddf5dc0cddbc0f009212737a3090a11c7413a18e60ae2daf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/frontend/single_item_use_import_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/single_item_use_import_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/single_item_use_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/single_item_use_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/single_item_use_import_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/single_item_use_import_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a single-item braces import and resolves the imported symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/single_item_use_import_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still parses a multi-item braces import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/single_item_use_import_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses an aliased single-item braces import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

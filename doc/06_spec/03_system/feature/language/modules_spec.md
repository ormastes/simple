# Module System Specification - Test Specification

> This file contains executable test cases extracted from modules.md. The original specification file remains as architectural reference documentation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module System Specification - Test Specification

This file contains executable test cases extracted from modules.md. The original specification file remains as architectural reference documentation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Reference |
| Type | Extracted Examples (Category B) |
| Reference | modules.md |
| Source | `test/03_system/feature/language/modules_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This file contains executable test cases extracted from modules.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/06_spec/feature/language/modules_spec.md

## Extracted Test Cases

Tests cover module declaration, visibility rules, selective imports,
re-exports, dependency tracking, and circular-dependency detection.

## Syntax

Declare a module and export items:

    module math:
        pub fn add(a: i64, b: i64) -> i64: a + b
        fn internal(): ...  # private to module

Import selectively:

    use std.math.{add, sqrt}
    use std.collections.{HashMap, HashSet}

Re-export from a facade module:

    pub use inner.{Foo, Bar}

Wildcard import (use sparingly):

    use std.prelude.*

## Examples

    val m = ModuleRecord.new("math")
    m.export("add")
    m.export("sqrt")
    m.exports  # => ["add", "sqrt"]

    m.add_dep("std.core")
    m.depends_on("std.core")  # => true

    val resolver = ModuleResolver.new()
    resolver.register(m)
    resolver.resolve("math.add")  # => found: "math.add"

    resolver.has_cycle("math", "std.core")  # => false

## Key Concepts

**Module** — a named namespace that groups related declarations. A module
corresponds to a single `.spl` file or a directory with an `index.spl`.

**Visibility** — items are private by default. `pub` makes them accessible
outside the declaring module. `pub(crate)` restricts visibility to the
current compilation unit.

**Selective import** — `use module.{A, B}` imports named items without
polluting the local namespace with unintended names.

**Re-export** — `pub use inner.{Foo}` lifts items from a private inner
module into a public facade, letting callers import from one stable path
regardless of internal structure changes.

**Circular dependencies** — the compiler detects and rejects import cycles.
Refactor by extracting shared code into a common module that both depend on.

**Path resolution** — `use std.X` always resolves from `src/lib/`. Relative
paths use `use super.X` (parent) or `use self.X` (current module).

**Namespace hygiene** — each module has its own scope. Names defined in one
module never shadow names in another unless explicitly imported.

## Common Patterns

Facade module (stable public API over reorganised internals):

    # lib/http/mod.spl
    pub use self.client.{Client, Response}
    pub use self.server.{Server, Handler}

Feature-gated module (conditional compilation):

    #[cfg(feature = "tls")]
    use self.tls.{TlsStream}

Module aliasing for long paths:

    use std.collections.hashmap as hm
    val m = hm.HashMap.new()

Inline test module (collocated tests, not in test/):

    #[cfg(test)]
    module tests:
        use super.*
        it "round_trip":
            # @req REQ-SSPEC-SYSTEM
            step("round_trip")
            ...

## Scenarios

### Module System Spec

#### tracks module metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tracks module metadata
   - Expected: module.export_count() equals `2`
   - Expected: module.dependency_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks module metadata")
val module = ModuleRecord.new("app.main", ["run", "config"], ["std.io"])
expect(module.export_count()).to_equal(2)
expect(module.dependency_count()).to_equal(1)
```

</details>

#### resolves dependency order before root

- resolves dependency order before root
   - Expected: order[0] equals `std.io`
   - Expected: order[1] equals `app.config`
   - Expected: order[2] equals `app.main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves dependency order before root")
val io = ModuleRecord.new("std.io", ["print"], [])
val config = ModuleRecord.new("app.config", ["load"], ["std.io"])
val root = ModuleRecord.new("app.main", ["run"], ["std.io", "app.config"])
val order = resolve_load_order(root, [io, config])
expect(order[0]).to_equal("std.io")
expect(order[1]).to_equal("app.config")
expect(order[2]).to_equal("app.main")
```

</details>

#### checks exported symbols

- checks exported symbols
   - Expected: module.exports_symbol("sum") is true
   - Expected: module.exports_symbol("min") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks exported symbols")
val module = ModuleRecord.new("math", ["sum", "avg"], [])
expect(module.exports_symbol("sum")).to_equal(true)
expect(module.exports_symbol("min")).to_equal(false)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4a578e606534ad1a27c78ab6b934f2a3c41ad6d75e9fea40dfa1a9a14e3c387f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a578e606534ad1a27c78ab6b934f2a3c41ad6d75e9fea40dfa1a9a14e3c387f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a578e606534ad1a27c78ab6b934f2a3c41ad6d75e9fea40dfa1a9a14e3c387f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/language/modules_spec.spl
mirror: doc/06_spec/03_system/feature/language/modules_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/language/modules_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/language/modules_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/language/modules_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/language/modules_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks module metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/modules_spec.spl:156:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves dependency order before root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/modules_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks exported symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

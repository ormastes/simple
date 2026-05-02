# Module System Specification - Test Specification

This file contains executable test cases extracted from modules.md. The original specification file remains as architectural reference documentation.

## At a Glance

| Field | Value |
|-------|-------|
| Status | Reference |
| Type | Extracted Examples (Category B) |
| Reference | modules.md |
| Source | `test/specs/modules_spec.spl` |
| Updated | 2026-04-24 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

This file contains executable test cases extracted from modules.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/06_spec/modules.md

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
            ...

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `summary.txt` | Text artifact | `build/test-artifacts/specs/modules/summary.txt` |

## Scenarios

- round_trip
- tracks module metadata
- resolves dependency order before root
- checks exported symbols

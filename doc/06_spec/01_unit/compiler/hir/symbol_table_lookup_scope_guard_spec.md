# `SymbolTable.lookup`/`lookup_or_invalid` survive an out-of-range `current_scope` (lane SYM-SCOPE-GUARD)

> Filed bug `doc/08_tracking/bug/stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06.md`: `SymbolTable.lookup()` traps with a SIGILL ("field access on nil receiver") under native codegen when `self.current_scope` (or a scope reached by walking `scope.parent`) references a `scope_id` that was never pushed into `self.scopes`. Two guard strategies were already tried and reverted:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `SymbolTable.lookup`/`lookup_or_invalid` survive an out-of-range `current_scope` (lane SYM-SCOPE-GUARD)

Filed bug `doc/08_tracking/bug/stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06.md`: `SymbolTable.lookup()` traps with a SIGILL ("field access on nil receiver") under native codegen when `self.current_scope` (or a scope reached by walking `scope.parent`) references a `scope_id` that was never pushed into `self.scopes`. Two guard strategies were already tried and reverted:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / HIR |
| Status | Active |
| Source | `test/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Filed bug `doc/08_tracking/bug/stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06.md`:
`SymbolTable.lookup()` traps with a SIGILL ("field access on nil receiver")
under native codegen when `self.current_scope` (or a scope reached by
walking `scope.parent`) references a `scope_id` that was never pushed into
`self.scopes`. Two guard strategies were already tried and reverted:

1. No guard at all -> nil-receiver `ud2` trap on the bracket read
   `self.scopes[scope_id.id]`.
2. `if not rt_dict_contains(self.scopes, scope_id.id): break` -> `1ea6599e8fb`,
   reverted by `030ff43e330` -- `rt_dict_contains` under-reports membership on
   this struct-valued `Dict<i64, Scope>` under native codegen, so the guard
   made `lookup()` return constant `nil`, disabling the only recursion
   breakers in a mutual-recursion cycle and causing a stack overflow instead.

This spec pins down the THIRD approach landed in this session: `self.scopes`
is append-only (`push_scope` is the only writer, always inserting before
advancing `next_scope_id`; nothing ever removes a key), so
`scope_id.id in self.scopes` is EXACTLY `0 <= scope_id.id < next_scope_id` --
a plain scalar `i64` comparison, not a `Dict` operation, so it cannot exhibit
the `rt_dict_contains` false-negative bug. `next_scope_id` is a class field
(scalar `i64`), untouched by any of the documented struct-valued-Dict
pitfalls in `doc/07_guide/language/dict_native_pitfalls.md`.

Correct miss semantics (confirmed by reading `lookup`'s existing scope-chain
walk and by `lookup_or_invalid`'s pre-existing `SymbolId(id: -1)` sentinel):
an unregistered/out-of-range `scope_id` must behave exactly like "no parent"
-- the loop breaks and the function returns its normal miss value (`nil` for
`lookup`, `SymbolId(id: -1)` for `lookup_or_invalid`). It must NOT crash and
must NOT silently short-circuit lookups that would otherwise have found a
symbol in a *valid* scope reached before the corruption.

## Scenarios

### SymbolTable.lookup / lookup_or_invalid tolerate an out-of-range current_scope

#### lookup() finds a name defined in the (valid) root scope

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lookup() finds a name defined in the (valid) root scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lookup() finds a name defined in the (valid) root scope")
var symbols = SymbolTable.new()
val id = symbols.define(
    "RootThing",
    SymbolKind.Struct,
    nil,
    Span.empty(),
    Visibility.Private,
    false,
    nil
)

match symbols.lookup("RootThing"):
    case Some(found): expect(found.id).to_equal(id.id)
    case nil: expect(false).to_equal(true)
```

</details>

#### lookup() walks up a pushed child scope to find a root-scope name, then pop_scope restores it

- lookup() walks up a pushed child scope to find a root-scope name, then pop_scope restores it


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lookup() walks up a pushed child scope to find a root-scope name, then pop_scope restores it")
var symbols = SymbolTable.new()
val id = symbols.define(
    "OuterThing",
    SymbolKind.Struct,
    nil,
    Span.empty(),
    Visibility.Private,
    false,
    nil
)
symbols.push_scope(ScopeKind.Block)
symbols.define(
    "InnerThing",
    SymbolKind.Variable,
    nil,
    Span.empty(),
    Visibility.Private,
    true,
    nil
)

# Inner-scope name is visible from the child scope.
match symbols.lookup("InnerThing"):
    case Some(_): expect(true).to_equal(true)
    case nil: expect(false).to_equal(true)

# Outer-scope name is still reachable by walking scope.parent.
match symbols.lookup("OuterThing"):
    case Some(found): expect(found.id).to_equal(id.id)
    case nil: expect(false).to_equal(true)

symbols.pop_scope()

# After popping, the inner-only name is no longer visible.
match symbols.lookup("InnerThing"):
    case Some(_): expect(false).to_equal(true)
    case nil: expect(true).to_equal(true)

# Root name is still visible.
match symbols.lookup("OuterThing"):
    case Some(found): expect(found.id).to_equal(id.id)
    case nil: expect(false).to_equal(true)
```

</details>

#### lookup() does not crash and returns nil when current_scope was never pushed

- lookup() does not crash and returns nil when current_scope was never pushed


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lookup() does not crash and returns nil when current_scope was never pushed")
var symbols = SymbolTable.new()
symbols.define(
    "SomeThing",
    SymbolKind.Struct,
    nil,
    Span.empty(),
    Visibility.Private,
    false,
    nil
)

# Simulate the corrupted/invalid scope_id from the filed bug: a scope
# id that is >= next_scope_id, i.e. was never inserted into
# self.scopes by push_scope. This must not trap.
symbols.current_scope = ScopeId(id: 999)

match symbols.lookup("SomeThing"):
    case Some(_): expect(false).to_equal(true)
    case nil: expect(true).to_equal(true)

# A name that does exist, but is unreachable because the (bogus)
# current_scope has no valid parent chain back to root, must also
# miss cleanly rather than crash.
match symbols.lookup("DoesNotExist"):
    case Some(_): expect(false).to_equal(true)
    case nil: expect(true).to_equal(true)
```

</details>

#### lookup_or_invalid() returns SymbolId(id: -1) (is_valid() false) when current_scope is out of range

- lookup_or_invalid() returns SymbolId(id: -1) (is_valid() false) when current_scope is out of range
   - Expected: result.is_valid() is false
   - Expected: result.id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lookup_or_invalid() returns SymbolId(id: -1) (is_valid() false) when current_scope is out of range")
var symbols = SymbolTable.new()
symbols.current_scope = ScopeId(id: 12345)

val result = symbols.lookup_or_invalid("whatever")
expect(result.is_valid()).to_equal(false)
expect(result.id).to_equal(-1)
```

</details>

#### a negative current_scope id also breaks cleanly instead of crashing

- a negative current_scope id also breaks cleanly instead of crashing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a negative current_scope id also breaks cleanly instead of crashing")
var symbols = SymbolTable.new()
symbols.current_scope = ScopeId(id: -7)

match symbols.lookup("anything"):
    case Some(_): expect(false).to_equal(true)
    case nil: expect(true).to_equal(true)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `924868281cfa6af95cdf01e12fb7163520208e898b0b4debfc53be3e4a7ecb1f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `924868281cfa6af95cdf01e12fb7163520208e898b0b4debfc53be3e4a7ecb1f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `924868281cfa6af95cdf01e12fb7163520208e898b0b4debfc53be3e4a7ecb1f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lookup() finds a name defined in the (valid) root scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lookup() walks up a pushed child scope to find a root-scope name, then pop_scope restores it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lookup() does not crash and returns nil when current_scope was never pushed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

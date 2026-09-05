# EVERY `self.scopes[...]` bracket read in `SymbolTable` survives a corrupted `current_scope` (lane SYM-SCOPE-GUARD)

> This is the **similar-problem detection** spec for the defect class filed as `doc/08_tracking/bug/stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06.md`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# EVERY `self.scopes[...]` bracket read in `SymbolTable` survives a corrupted `current_scope` (lane SYM-SCOPE-GUARD)

This is the **similar-problem detection** spec for the defect class filed as `doc/08_tracking/bug/stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06.md`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / HIR |
| Status | Active |
| Source | `test/01_unit/compiler/hir/symbol_table_scope_bracket_read_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This is the **similar-problem detection** spec for the defect class filed as
`doc/08_tracking/bug/stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06.md`.

That bug is usually described as "`SymbolTable.lookup` traps ud2 / field
access on nil receiver". But `lookup` is not special: the trap comes from an
**unguarded bracket read of `self.scopes` keyed by a scope id that was never
pushed**. `self.scopes` is a struct-valued `Dict<i64, Scope>`, and under
native codegen a bracket read that misses yields a nil receiver whose first
field access is a fatal `ud2`, not a recoverable miss.

The landed fix guarded exactly two of the reads (`lookup` and
`lookup_or_invalid`). `hir_types.spl` contains **five** reads of
`self.scopes[...]`; the other three — two in `declare`, one in `pop_scope` —
were left bare and are reachable with the same corrupted `current_scope` that
the filed bug's own root-cause candidate #1 postulates ("`self.current_scope`
reads back corrupted/stale under native codegen"). A guard on `lookup` alone
does not close the class.

So this spec asserts the **invariant**, not the one function: for a corrupted
or never-pushed `current_scope`, no `SymbolTable` entry point may reach a
`self.scopes[...]` read with an out-of-range key. Each example drives a
*different* entry point, so re-guarding one function cannot make the whole
file pass.

It also pins the ordering precondition the guards depend on. All of them use
`0 <= id < next_scope_id` as an EXACT substitute for `id in self.scopes`
(deliberately, because `rt_dict_contains` on this struct-valued dict
under-reports and that guard strategy was already tried and reverted in
`030ff43e330`). That identity holds only if `push_scope` inserts into
`self.scopes` BEFORE advancing `next_scope_id`; if the counter ever leads the
dict, the range check admits a key the dict does not have and every guard in
the file silently reverts to the unguarded, trapping behaviour.

**Engine scope, stated honestly.** The `ud2` symptom is native-codegen only.
A spec body runs interpreted, so this file cannot and does not claim the
native trap is gone. What it does check is engine-independent and is the
thing the fix actually changes: that the source-level control flow refuses to
perform an out-of-range scope read at all, from every entry point, so there
is no bracket read left for native codegen to turn into a trap. Confirming
the native lane additionally requires a working self-hosted `native-build`.

## Scenarios

### SymbolTable scope-dict bracket reads are guarded at every entry point

#### declare() of a non-type symbol does not read an out-of-range scope

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- declare() of a non-type symbol does not read an out-of-range scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declare() of a non-type symbol does not read an out-of-range scope")
var symbols = SymbolTable.new()
# The corrupted / never-pushed scope id from the filed bug.
symbols.current_scope = ScopeId(id: 999)

val id = symbols.define(
    "LateVariable",
    SymbolKind.Variable,
    nil,
    Span.empty(),
    Visibility.Private,
    true,
    nil
)

# It must have produced a real symbol id, not crashed and not
# returned a sentinel.
expect(id.id).to_be_greater_than(-1)

# Having recovered to the always-present root scope, the name must be
# findable again -- a guard that merely swallowed the write would
# leave this unresolvable and is not acceptable.
match symbols.lookup("LateVariable"):
    case Some(found): expect(found.id).to_equal(id.id)
    case nil: expect(false).to_equal(true)
```

</details>

#### declare() of a TYPE symbol takes the first-write-wins path without an out-of-range read

- declare() of a TYPE symbol takes the first-write-wins path without an out-of-range read
   - Expected: second.id equals `first.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declare() of a TYPE symbol takes the first-write-wins path without an out-of-range read")
# Type symbols take a SEPARATE, earlier bracket read in declare()
# than the one non-type symbols reach, so this is a distinct site.
var symbols = SymbolTable.new()
symbols.current_scope = ScopeId(id: -3)

val first = symbols.define(
    "LateStruct",
    SymbolKind.Struct,
    nil,
    Span.empty(),
    Visibility.Private,
    false,
    nil
)
expect(first.id).to_be_greater_than(-1)

# First-write-wins must still hold after the recovery.
val second = symbols.define(
    "LateStruct",
    SymbolKind.Struct,
    nil,
    Span.empty(),
    Visibility.Private,
    false,
    nil
)
expect(second.id).to_equal(first.id)
```

</details>

#### pop_scope() does not read an out-of-range scope

- pop_scope() does not read an out-of-range scope
   - Expected: symbols.current_scope.id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pop_scope() does not read an out-of-range scope")
var symbols = SymbolTable.new()
symbols.current_scope = ScopeId(id: 4242)

symbols.pop_scope()

# There is no parent to walk to from a bogus id; the only safe
# resting place is the always-present root scope.
expect(symbols.current_scope.id).to_equal(0)
```

</details>

#### pop_scope() still performs a REAL pop when the scope id is valid

- pop_scope() still performs a REAL pop when the scope id is valid
   - Expected: symbols.current_scope.id equals `pushed.id`
   - Expected: symbols.current_scope.id equals `outer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pop_scope() still performs a REAL pop when the scope id is valid")
# Guards against a "break too eagerly" regression: the fix must not
# turn pop_scope into a no-op for legitimate scopes.
var symbols = SymbolTable.new()
val outer = symbols.current_scope.id
val pushed = symbols.push_scope(ScopeKind.Block)
expect(symbols.current_scope.id).to_equal(pushed.id)

symbols.pop_scope()
expect(symbols.current_scope.id).to_equal(outer)
```

</details>

#### push_scope inserts into scopes before advancing next_scope_id

- push_scope inserts into scopes before advancing next_scope_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("push_scope inserts into scopes before advancing next_scope_id")
# The precondition every range guard in the file relies on: the
# counter must never lead the dict, or `0 <= id < next_scope_id`
# stops being an exact substitute for dict membership and each guard
# silently degrades to the unguarded, trapping behaviour.
var symbols = SymbolTable.new()
val pushed = symbols.push_scope(ScopeKind.Block)

# The freshly pushed id must be strictly inside the admitted range...
expect(pushed.id).to_be_less_than(symbols.next_scope_id)

# ...and must genuinely be readable, i.e. the dict really does have
# the key the range check now admits.
symbols.define(
    "InsideFreshScope",
    SymbolKind.Variable,
    nil,
    Span.empty(),
    Visibility.Private,
    true,
    nil
)
match symbols.lookup("InsideFreshScope"):
    case Some(_): expect(true).to_equal(true)
    case nil: expect(false).to_equal(true)
```

</details>

#### the id one past the end is never admitted

- the id one past the end is never admitted
   - Expected: symbols.lookup_or_invalid("anything").is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the id one past the end is never admitted")
var symbols = SymbolTable.new()
symbols.current_scope = ScopeId(id: symbols.next_scope_id)

match symbols.lookup("anything"):
    case Some(_): expect(false).to_equal(true)
    case nil: expect(true).to_equal(true)

expect(symbols.lookup_or_invalid("anything").is_valid()).to_equal(false)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9fe1dd51ab7e6a9f5a03f959bf27fbc18a4c4886807057b9cd5dc986cbdba577`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fe1dd51ab7e6a9f5a03f959bf27fbc18a4c4886807057b9cd5dc986cbdba577`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fe1dd51ab7e6a9f5a03f959bf27fbc18a4c4886807057b9cd5dc986cbdba577`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/hir/symbol_table_scope_bracket_read_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/symbol_table_scope_bracket_read_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/symbol_table_scope_bracket_read_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/symbol_table_scope_bracket_read_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/symbol_table_scope_bracket_read_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/symbol_table_scope_bracket_read_class_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declare() of a non-type symbol does not read an out-of-range scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/symbol_table_scope_bracket_read_class_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declare() of a TYPE symbol takes the first-write-wins path without an out-of-range read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/symbol_table_scope_bracket_read_class_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pop_scope() does not read an out-of-range scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

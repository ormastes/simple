# `SymbolTable.get_symbol` retrieves the FIRST-registered symbol (id 0) (lane SYM0 get-symbol-id-zero-nil)

> Filed bug `doc/08_tracking/bug/hir_get_symbol_id_zero_returns_nil_2026-07-29.md`: `SymbolTable.get_symbol(SymbolId(id: 0))` returned `nil` for a validly registered symbol, even though `lookup(name)` correctly resolved the same symbol to `SymbolId(id: 0)`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `SymbolTable.get_symbol` retrieves the FIRST-registered symbol (id 0) (lane SYM0 get-symbol-id-zero-nil)

Filed bug `doc/08_tracking/bug/hir_get_symbol_id_zero_returns_nil_2026-07-29.md`: `SymbolTable.get_symbol(SymbolId(id: 0))` returned `nil` for a validly registered symbol, even though `lookup(name)` correctly resolved the same symbol to `SymbolId(id: 0)`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / HIR |
| Status | Active |
| Source | `test/01_unit/compiler/hir/symbol_table_id_zero_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Filed bug `doc/08_tracking/bug/hir_get_symbol_id_zero_returns_nil_2026-07-29.md`:
`SymbolTable.get_symbol(SymbolId(id: 0))` returned `nil` for a validly
registered symbol, even though `lookup(name)` correctly resolved the same
symbol to `SymbolId(id: 0)`.

Root cause (confirmed via isolated probe, NOT an id-0/Dict-sentinel
collision): `get_symbol`'s `match id: case SymbolId(raw): ... case _: nil`
matched a bare struct-constructor pattern directly against the `SymbolId?`
(Option-wrapped) parameter. A naked `case SymbolId(raw):` pattern falls
through to the wildcard arm for EVERY id (0, 1, 2, ...) when the value came
from a `return`-based helper like `lookup` -- only the `case
Some(SymbolId(raw)):` shape (used everywhere else in the codebase, e.g.
`hir_symbol_table_all_functions_spec.spl`) reliably unwraps it. `id 0` is an
entirely ordinary, validly-allocated id (`SymbolId.is_valid()` already treats
it as such) -- this spec pins that invariant down: every registered symbol,
INCLUDING the first one (id 0), must be retrievable via `get_symbol`.

## Scenarios

### SymbolTable.get_symbol round-trips the first-registered symbol (id 0)

#### the first symbol registered in a module (id 0) is retrievable via get_symbol

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the first symbol registered in a module (id 0) is retrievable via get_symbol
   - Expected: id.id equals `0`
   - Expected: false is true
   - Expected: found.name equals `first_fn`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the first symbol registered in a module (id 0) is retrievable via get_symbol")
val src = "fn first_fn() -> i64:\n    1\n"
val path = "src/symbol_table_id_zero_fixture.spl"
val log = make_logger()
val module = parse_full_frontend(src, path, "symbol_table_id_zero_fixture", log)
var lowering = HirLowering.with_filename(path)
val hir = lowering.lower_module(module)

val resolved_id = hir.symbols.lookup("first_fn")
match resolved_id:
    case Some(id):
        # This is the first symbol ever defined in a fresh SymbolTable,
        # so it MUST be id 0 -- the exact case the filed bug covers.
        expect(id.id).to_equal(0)
    case nil:
        expect(false).to_equal(true)

val sym = hir.symbols.get_symbol(resolved_id)
match sym:
    case Some(found):
        expect(found.name).to_equal("first_fn")
    case nil:
        expect(false).to_equal(true)
```

</details>

#### lookup and get_symbol round-trip for several symbols, including the first (id 0)

- lookup and get_symbol round-trip for several symbols, including the first (id 0)
   - Expected: found.name equals `name`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lookup and get_symbol round-trip for several symbols, including the first (id 0)")
val src = "fn first_fn() -> i64:\n" +
    "    1\n" +
    "struct Point:\n" +
    "    x: i64\n" +
    "fn second_fn() -> i64:\n" +
    "    2\n" +
    "enum Color:\n" +
    "    Red\n" +
    "    Green\n"
val path = "src/symbol_table_id_zero_roundtrip_fixture.spl"
val log = make_logger()
val module = parse_full_frontend(src, path, "symbol_table_id_zero_roundtrip_fixture", log)
var lowering = HirLowering.with_filename(path)
val hir = lowering.lower_module(module)

var names: [text] = []
names = names.push("first_fn")
names = names.push("Point")
names = names.push("second_fn")
names = names.push("Color")

var idx = 0
while idx < names.len():
    val name = names[idx]
    val resolved = hir.symbols.lookup(name)
    match resolved:
        case Some(id):
            val sym = hir.symbols.get_symbol(resolved)
            match sym:
                case Some(found):
                    expect(found.name).to_equal(name)
                case nil:
                    expect(false).to_equal(true)
        case nil:
            expect(false).to_equal(true)
    idx = idx + 1
```

</details>

#### an id that was never registered still yields nil from get_symbol

- an id that was never registered still yields nil from get_symbol
   - Expected: false is true
   - Expected: true is true
   - Expected: unknown.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("an id that was never registered still yields nil from get_symbol")
val src = "fn only_fn() -> i64:\n    1\n"
val path = "src/symbol_table_id_zero_invalid_fixture.spl"
val log = make_logger()
val module = parse_full_frontend(src, path, "symbol_table_id_zero_invalid_fixture", log)
var lowering = HirLowering.with_filename(path)
val hir = lowering.lower_module(module)

val bogus_id: SymbolId? = Some(SymbolId(id: 999999))
val missing = hir.symbols.get_symbol(bogus_id)
match missing:
    case Some(_):
        expect(false).to_equal(true)
    case nil:
        expect(true).to_equal(true)

val unknown = hir.symbols.lookup_or_invalid("this_name_was_never_declared")
expect(unknown.is_valid()).to_equal(false)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7fee586d455632085a66b9369e3b944846e04535d236252595be26d239e9f4de`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7fee586d455632085a66b9369e3b944846e04535d236252595be26d239e9f4de`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7fee586d455632085a66b9369e3b944846e04535d236252595be26d239e9f4de`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/hir/symbol_table_id_zero_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/symbol_table_id_zero_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/symbol_table_id_zero_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/symbol_table_id_zero_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/symbol_table_id_zero_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/symbol_table_id_zero_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the first symbol registered in a module (id 0) is retrievable via get_symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/symbol_table_id_zero_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lookup and get_symbol round-trip for several symbols, including the first (id 0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/symbol_table_id_zero_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an id that was never registered still yields nil from get_symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

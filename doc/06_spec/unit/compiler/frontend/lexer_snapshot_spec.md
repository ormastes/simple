# Lexer Snapshot Specification

> Tests covering typed lexer snapshots.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Snapshot Specification

## Scenarios

### typed lexer snapshots

#### copies the indent stack and keeps restore free of text serialization

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- copies the indent stack and keeps restore free of text serialization
   - Expected: source does not contain `saved_indent_raw`
   - Expected: source does not contain `current_core_indent_stack_set(restored_indent_stack)`
   - Expected: source does not contain `current_core_indent_stack_parse(saved_indent_raw)`
   - Expected: source does not contain `lex_cur_kind_set(saved_kind)`
   - Expected: source does not contain `current_core_lexer_slot`
   - Expected: parser does not contain `par_kind_slot`
   - Expected: parser does not contain `par_text_slot`
   - Expected: parser does not contain `par_line_slot`
   - Expected: parser does not contain `par_col_slot`
   - Expected: parser does not contain `par_env_save_slot`
   - Expected: decl_nodes does not contain `ast_decl_count_slot`
   - Expected: decl_nodes does not contain `ast_module_decl_count_slot`
   - Expected: decl_nodes does not contain `ast_decl_mirror_high_slot`
   - Expected: decl_nodes does not contain `ast_module_decl_mirror_high_slot`
   - Expected: stmts does not contain `lex_snapshot_restore(`
   - Expected: expr does not contain `lex_snapshot_restore(`
   - Expected: decls does not contain `lex_snapshot_restore(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 90 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copies the indent stack and keeps restore free of text serialization")
val source = rt_file_read_text("src/compiler/10.frontend/core/lexer.spl") ?? ""
expect(source).to_contain("struct LexSnapshot:")
expect(source).to_contain("indent_stack: [i64]")
expect(source).to_contain("for indent in lx.indent_stack:")
expect(source).to_contain("indent_stack: saved_indent_stack")
expect(source).to_contain("lx.indent_stack = snapshot.indent_stack")
expect(source).to_contain("fn lex_snapshot_release(snapshot: LexSnapshot, release_indent_stack: bool):")
expect(source).to_contain("rt_array_free(snapshot.nums)")
expect(source).to_contain("rt_array_free(snapshot.texts)")
expect(source).to_contain("rt_array_free(snapshot.indent_stack)")
expect(source).to_contain("rt_array_free(lx.indent_stack)")
expect(source).to_contain("lex_snapshot_release(snapshot, false)")
expect(source).to_contain("lex_snapshot_release(snapshot, true)")
expect(source).to_contain("lx.cur_kind = nums[10]")
expect(source).to_contain("lex_generic_close_pending[0] = nums[11] == 1")
expect(source).to_contain("lex_cur_kind_direct[0] = saved_kind")
expect(source).to_contain("current_core_lexer_save(loaded)\n    val env_save = lex_env_save_enabled[0]")
expect(source).to_contain("if env_save:")
expect(source.contains("saved_indent_raw")).to_equal(false)
expect(source.contains("current_core_indent_stack_set(restored_indent_stack)")).to_equal(false)
expect(source.contains("current_core_indent_stack_parse(saved_indent_raw)")).to_equal(false)
expect(source.contains("lex_cur_kind_set(saved_kind)")).to_equal(false)
expect(source).to_contain("explicit lexer boundary paths")
expect(source).to_contain("fn lex_snapshot_restore(snapshot: LexSnapshot):")
# The active CoreLexer owns aggregate source/indent buffers directly;
# a one-element aggregate cache can survive an AST reset with retired
# payloads.  Its liveness bit makes every recovery path rebuild a
# fresh owner, and release must drop that owner before its mirrors.
expect(source).to_contain("var current_core_lexer: CoreLexer = make_core_lexer(\"\")")
expect(source).to_contain("var current_core_lexer_live: bool = false")
expect(source).to_contain("current_core_lexer = make_core_lexer(core_source)\n    current_core_lexer_live = true")
expect(source).to_contain("if not current_core_lexer_live:\n        current_core_lexer = current_core_lexer_load()\n        current_core_lexer_live = true")
expect(source).to_contain("pub fn lexer_release_parse_source_globals():")
expect(source).to_contain("current_core_lexer = make_core_lexer(\"\")\n    current_core_lexer_live = false")
expect(source.contains("current_core_lexer_slot")).to_equal(false)

val parser = rt_file_read_text("src/compiler/10.frontend/core/parser.spl") ?? ""
# Parser token state has the same reset boundary, but is scalar data.
# Keep recovery opt-in cached as a scalar too; no aggregate cache may
# be consulted after ast_reset() starts a new source.
expect(parser).to_contain("var par_kind_cached: i64 = 0")
expect(parser).to_contain("var par_text_cached: text = \"\"")
expect(parser).to_contain("var par_line_cached: i64 = 0")
expect(parser).to_contain("var par_col_cached: i64 = 0")
expect(parser).to_contain("var par_env_save_cached: i64 = -1")
expect(parser).to_contain("par_kind_cached = 0\n    par_text_cached = \"\"\n    par_line_cached = 0\n    par_col_cached = 0")
expect(parser).to_contain("fn par_kind_set(value: i64):\n    par_kind_cached = value")
expect(parser).to_contain("fn par_text_set(value: text):\n    par_text_cached = value")
expect(parser.contains("par_kind_slot")).to_equal(false)
expect(parser.contains("par_text_slot")).to_equal(false)
expect(parser.contains("par_line_slot")).to_equal(false)
expect(parser.contains("par_col_slot")).to_equal(false)
expect(parser.contains("par_env_save_slot")).to_equal(false)

# Decl count and env-mirror high-water state crosses the same reset
# boundary. Keep these four values scalar so native reset cannot
# retain a retired aggregate cache.
val decl_nodes = rt_file_read_text("src/compiler/10.frontend/core/_Ast/decl_nodes.spl") ?? ""
expect(decl_nodes).to_contain("var ast_decl_count_cached: i64 = 0")
expect(decl_nodes).to_contain("var ast_module_decl_count_cached: i64 = 0")
expect(decl_nodes).to_contain("var ast_decl_mirror_high_cached: i64 = 0")
expect(decl_nodes).to_contain("var ast_module_decl_mirror_high_cached: i64 = 0")
expect(decl_nodes.contains("ast_decl_count_slot")).to_equal(false)
expect(decl_nodes.contains("ast_module_decl_count_slot")).to_equal(false)
expect(decl_nodes.contains("ast_decl_mirror_high_slot")).to_equal(false)
expect(decl_nodes.contains("ast_module_decl_mirror_high_slot")).to_equal(false)

# Mirror entries must be dropped while their high-water marks survive;
# count reset follows only after the clear in ast_reset().
val module_state = rt_file_read_text("src/compiler/10.frontend/core/_Ast/module_state.spl") ?? ""
expect(module_state).to_contain("ast_decl_env_mirror_clear()\n    ast_module_decl_slots_clear()")
expect(module_state).to_contain("ast_decl_count_set(0)\n    ast_module_decl_count_set(0)")
# Compare the real call sequences (two-line snippets) so a prose
# comment mentioning ast_decl_count_set(0) cannot win the index race.
expect(module_state.index_of("ast_decl_env_mirror_clear()\n    ast_module_decl_slots_clear()")).to_be_less_than(module_state.index_of("ast_decl_count_set(0)\n    ast_module_decl_count_set(0)"))

val stmts = rt_file_read_text("src/compiler/10.frontend/core/parser_stmts.spl") ?? ""
val expr = rt_file_read_text("src/compiler/10.frontend/core/parser_expr.spl") ?? ""
val decls = rt_file_read_text("src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl") ?? ""
expect(stmts.contains("lex_snapshot_restore(")).to_equal(false)
expect(expr.contains("lex_snapshot_restore(")).to_equal(false)
expect(decls.contains("lex_snapshot_restore(")).to_equal(false)
expect(stmts).to_contain("lex_snapshot_commit(")
expect(stmts).to_contain("lex_snapshot_rollback(")
expect(expr).to_contain("lex_snapshot_commit(")
expect(expr).to_contain("lex_snapshot_rollback(")
expect(decls).to_contain("lex_snapshot_commit(")
expect(decls).to_contain("lex_snapshot_rollback(")
```

</details>

#### preserves nested parser indentation across repeated speculation

- preserves nested parser indentation across repeated speculation
   - Expected: parser_has_errors() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves nested parser indentation across repeated speculation")
val source = "fn main() -> i64:\n" +
    "    if true:\n" +
    "        val nested = 1\n" +
    "        nested\n" +
    "    0\n"
var round = 0
while round < 8:
    ast_reset()
    parse_module(source, "lexer_snapshot_spec.spl")
    expect(parser_has_errors()).to_equal(false)
    round = round + 1
```

</details>

#### keeps repeated source character access at a memory plateau

- keeps repeated source character access at a memory plateau
   - Expected: observed equals `e`
   - Expected: after_live equals `before_live`
   - Expected: after_aux equals `before_aux`
   - Expected: after_capacity equals `before_capacity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps repeated source character access at a memory plateau")
lex_init("abcdefghij")
var warmup = 0
while warmup < 8:
    lex_source_char_at(4)
    warmup = warmup + 1

val before_live = rt_heap_live_bytes()
val before_aux = rt_heap_aux_live_bytes()
val before_capacity = rt_heap_array_capacity_bytes()
var observed = ""
var round = 0
while round < 4096:
    observed = lex_source_char_at(4)
    round = round + 1

val after_live = rt_heap_live_bytes()
val after_aux = rt_heap_aux_live_bytes()
val after_capacity = rt_heap_array_capacity_bytes()
expect(observed).to_equal("e")
expect(after_live).to_equal(before_live)
expect(after_aux).to_equal(before_aux)
expect(after_capacity).to_equal(before_capacity)
```

</details>

#### keeps successful repeated speculation within live memory budgets

- keeps successful repeated speculation within live memory budgets
   - Expected: parser_has_errors() is false
   - Expected: parser_has_errors() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps successful repeated speculation within live memory budgets")
val source = "fn main() -> i64:\n" +
    "    val value = make<i64>()\n" +
    "    if true:\n" +
    "        val nested = value\n" +
    "        nested\n" +
    "    0\n"
var warmup = 0
while warmup < 3:
    ast_reset()
    parse_module(source, "lexer_snapshot_memory_spec.spl")
    expect(parser_has_errors()).to_equal(false)
    warmup = warmup + 1
val before_live = rt_heap_live_bytes()
val before_aux = rt_heap_aux_live_bytes()
val before_capacity = rt_heap_array_capacity_bytes()
var previous_live = before_live
var previous_aux = before_aux
var previous_capacity = before_capacity
var round = 0
while round < 24:
    ast_reset()
    parse_module(source, "lexer_snapshot_memory_spec.spl")
    expect(parser_has_errors()).to_equal(false)
    val round_live = rt_heap_live_bytes()
    val round_aux = rt_heap_aux_live_bytes()
    val round_capacity = rt_heap_array_capacity_bytes()
    # Per-round slopes catch a renewed leak even if the aggregate
    # budget is raised for a slower but valid runtime.
    expect(round_live - previous_live).to_be_less_than(2 * 1024 * 1024)
    expect(round_aux - previous_aux).to_be_less_than(4 * 1024 * 1024)
    expect(round_capacity - previous_capacity).to_be_less_than(4 * 1024 * 1024)
    previous_live = round_live
    previous_aux = round_aux
    previous_capacity = round_capacity
    round = round + 1
val after_live = rt_heap_live_bytes()
val after_aux = rt_heap_aux_live_bytes()
val after_capacity = rt_heap_array_capacity_bytes()
# Fixed-N broad budgets tolerate allocator variation while catching the
# former per-restore text split/format fan-out.
expect(after_live - before_live).to_be_less_than(32 * 1024 * 1024)
expect(after_aux - before_aux).to_be_less_than(64 * 1024 * 1024)
expect(after_capacity - before_capacity).to_be_less_than(64 * 1024 * 1024)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/frontend/lexer_snapshot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering typed lexer snapshots.
- typed lexer snapshots

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5117c12c410a80a82e37ffdb4255326bf54bc35e138ee48d99d8ef5732f4b073`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5117c12c410a80a82e37ffdb4255326bf54bc35e138ee48d99d8ef5732f4b073`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5117c12c410a80a82e37ffdb4255326bf54bc35e138ee48d99d8ef5732f4b073`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/frontend/lexer_snapshot_spec.spl
mirror: doc/06_spec/unit/compiler/frontend/lexer_snapshot_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/compiler/frontend/lexer_snapshot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/frontend/lexer_snapshot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/frontend/lexer_snapshot_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/unit/compiler/frontend/lexer_snapshot_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copies the indent stack and keeps restore free of text serialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/frontend/lexer_snapshot_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves nested parser indentation across repeated speculation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/frontend/lexer_snapshot_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps repeated source character access at a memory plateau' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

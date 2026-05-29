# aop debug log
*Source:* `test/feature/usage/aop_debug_log_spec.spl`

## Feature: AOP Debug Logger

### Scenario: enable and disable

| # | Example | Status |
|---|---------|--------|
| 1 | starts disabled by default when SIMPLE_AOP_DEBUG not set | pass |
| 2 | enables with wildcard pattern | pass |
| 3 | enables with specific pattern | pass |
| 4 | disables logging | pass |

**Example:** starts disabled by default when SIMPLE_AOP_DEBUG not set
    Given val enabled = debug_log_is_enabled()
    Then  expect(enabled).to_equal(false)

**Example:** enables with wildcard pattern
    Then  expect(debug_log_is_enabled()).to_equal(true)
    Given val (en, pat, cnt, dep) = debug_log_get_status()
    Then  expect(en).to_equal(true)
    Then  expect(pat).to_equal("*")

**Example:** enables with specific pattern
    Given val (en, pat, cnt, dep) = debug_log_get_status()
    Then  expect(en).to_equal(true)
    Then  expect(pat).to_equal("parse_*")

**Example:** disables logging
    Then  expect(debug_log_is_enabled()).to_equal(false)

### Scenario: entry creation

| # | Example | Status |
|---|---------|--------|
| 1 | creates enter entry with correct fields | pass |
| 2 | creates exit entry paired with enter | pass |
| 3 | skips entries when disabled | pass |

**Example:** creates enter entry with correct fields
    Given val gid = debug_log_enter("my_func", "app.mcp.main", "Server", 42, "path=\"/src\"")
    Given val entries = debug_log_get_entries()
    Then  expect(entries.len()).to_equal(1)
    Given val e = entries[0]
    Then  expect(e.entry_type).to_equal("enter")
    Then  expect(e.function_name).to_equal("my_func")
    Then  expect(e.package_path).to_equal("app.mcp.main")
    Then  expect(e.class_name).to_equal("Server")
    Then  expect(e.line_number).to_equal(42)
    Then  expect(e.params_text).to_equal("path=\"/src\"")
    Then  expect(e.depth).to_equal(0)
    Then  expect(e.group_id).to_equal(gid)

**Example:** creates exit entry paired with enter
    Given val gid = debug_log_enter("my_func", "app.mcp.main", "", 10, "")
    Given val entries = debug_log_get_entries()
    Then  expect(entries.len()).to_equal(2)
    Then  expect(entries[0].entry_type).to_equal("enter")
    Then  expect(entries[1].entry_type).to_equal("exit")
    Then  expect(entries[0].group_id).to_equal(entries[1].group_id)

**Example:** skips entries when disabled
    Given val gid = debug_log_enter("my_func", "mod", "", 1, "")
    Then  expect(gid).to_equal(-1)
    Then  expect(debug_log_get_entries().len()).to_equal(0)

### Scenario: depth tracking

| # | Example | Status |
|---|---------|--------|
| 1 | tracks nested call depth | pass |

**Example:** tracks nested call depth
    Given val g1 = debug_log_enter("outer", "mod", "", 1, "")
    Given val g2 = debug_log_enter("inner", "mod", "", 2, "")
    Given val g3 = debug_log_enter("deep", "mod", "", 3, "")
    Given val entries = debug_log_get_entries()
    Then  expect(entries.len()).to_equal(6)
    Then  expect(entries[0].depth).to_equal(0)
    Then  expect(entries[1].depth).to_equal(1)
    Then  expect(entries[2].depth).to_equal(2)
    Then  expect(entries[3].depth).to_equal(2)
    Then  expect(entries[4].depth).to_equal(1)
    Then  expect(entries[5].depth).to_equal(0)

### Scenario: group pairing

| # | Example | Status |
|---|---------|--------|
| 1 | assigns unique group IDs | pass |
| 2 | tracks parent group IDs | pass |

**Example:** assigns unique group IDs
    Given val g1 = debug_log_enter("func_a", "mod", "", 1, "")
    Given val g2 = debug_log_enter("func_b", "mod", "", 2, "")
    Then  expect(g1).to_be_greater_than(0)
    Then  expect(g2).to_be_greater_than(g1)

**Example:** tracks parent group IDs
    Given val g_outer = debug_log_enter("outer", "mod", "", 1, "")
    Given val g_inner = debug_log_enter("inner", "mod", "", 2, "")
    Given val entries = debug_log_get_entries()
    Then  expect(entries[1].parent_group_id).to_equal(g_outer)
    Then  expect(entries[0].parent_group_id).to_equal(0)

### Scenario: filter pattern

| # | Example | Status |
|---|---------|--------|
| 1 | filters by prefix pattern | pass |
| 2 | filters by module path | pass |
| 3 | matches exact function name | pass |

**Example:** filters by prefix pattern
    Given val g1 = debug_log_enter("parse_expr", "mod", "", 1, "")
    Given val g2 = debug_log_enter("eval_expr", "mod", "", 2, "")
    Then  expect(g1).to_be_greater_than(0)
    Then  expect(g2).to_equal(-1)
    Then  expect(debug_log_get_entries().len()).to_equal(1)

**Example:** filters by module path
    Given val g1 = debug_log_enter("handle", "app.mcp.main", "", 1, "")
    Given val g2 = debug_log_enter("handle", "app.cli.main", "", 2, "")
    Then  expect(g1).to_be_greater_than(0)
    Then  expect(g2).to_equal(-1)

**Example:** matches exact function name
    Given val g1 = debug_log_enter("my_exact_func", "mod", "", 1, "")
    Given val g2 = debug_log_enter("other_func", "mod", "", 2, "")
    Then  expect(g1).to_be_greater_than(0)
    Then  expect(g2).to_equal(-1)

### Scenario: query entries

| # | Example | Status |
|---|---------|--------|
| 1 | returns entries since a given ID | pass |

**Example:** returns entries since a given ID
    Given val g1 = debug_log_enter("a", "mod", "", 1, "")
    Given val entries_before = debug_log_get_entries()
    Given val last_id = entries_before[entries_before.len() - 1].entry_id
    Given val g2 = debug_log_enter("b", "mod", "", 2, "")
    Given val new_entries = debug_log_get_entries_since(last_id)
    Then  expect(new_entries.len()).to_equal(2)
    Then  expect(new_entries[0].function_name).to_equal("b")

### Scenario: ring buffer

| # | Example | Status |
|---|---------|--------|
| 1 | trims entries when exceeding max | pass |

**Example:** trims entries when exceeding max
    Given val entries = debug_log_get_entries()
    Then  expect(entries.len()).to_be_less_than(26)

### Scenario: clear

| # | Example | Status |
|---|---------|--------|
| 1 | resets all state | pass |

**Example:** resets all state
    Given val (en, pat, cnt, dep) = debug_log_get_status()
    Then  expect(cnt).to_equal(0)
    Then  expect(dep).to_equal(0)



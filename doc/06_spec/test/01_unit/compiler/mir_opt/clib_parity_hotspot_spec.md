# CLibParityHotspot Specification

> Validates the CLibParityHotspot fact type in the optimization plugin, including the OptimizerProviderKind enum extension and the rule table with 3+ C-library-shape patterns: byte-copy, endian-load, checksum-reducer.

<!-- sdn-diagram:id=clib_parity_hotspot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=clib_parity_hotspot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

clib_parity_hotspot_spec -> std
clib_parity_hotspot_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=clib_parity_hotspot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 70 | 70 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLibParityHotspot Specification

Validates the CLibParityHotspot fact type in the optimization plugin, including the OptimizerProviderKind enum extension and the rule table with 3+ C-library-shape patterns: byte-copy, endian-load, checksum-reducer.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #hw-access-optimization-infra |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/pure_simple_lib_standalone_hw_plan.md |
| Source | `test/01_unit/compiler/mir_opt/clib_parity_hotspot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the CLibParityHotspot fact type in the optimization plugin,
including the OptimizerProviderKind enum extension and the rule table
with 3+ C-library-shape patterns: byte-copy, endian-load, checksum-reducer.

## Behavior

- CLibParityHotspot added to OptimizerProviderKind enum
- Factory function creates provider with required_facts and produced_facts
- Rule table returns at least 3 CLibParityRule entries
- Each rule has pattern_kind, intrinsic, cost_delta fields

## Scenarios

### CLibParityHotspot

### OptimizerProviderKind

#### AC-3: enum contains CLibParityHotspot variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = OptimizerProviderKind.CLibParityHotspot

val is_clib = kind == OptimizerProviderKind.CLibParityHotspot
expect(is_clib).to_equal(true)
```

</details>

### CLibPatternKind

#### AC-3: enum has ByteCopy variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.ByteCopy
val is_byte_copy = kind == CLibPatternKind.ByteCopy
expect(is_byte_copy).to_equal(true)
```

</details>

#### AC-3: enum has EndianLoad variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.EndianLoad
val is_endian = kind == CLibPatternKind.EndianLoad
expect(is_endian).to_equal(true)
```

</details>

#### AC-3: enum has ChecksumReducer variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.ChecksumReducer
val is_checksum = kind == CLibPatternKind.ChecksumReducer
expect(is_checksum).to_equal(true)
```

</details>

#### covers filesystem, database, webserver, and SimpleOS general patterns

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clib_parity_domain_rule_count("filesystem")).to_be_greater_than(0)
expect(clib_parity_domain_rule_count("database")).to_be_greater_than(0)
expect(clib_parity_domain_rule_count("webserver")).to_be_greater_than(0)
expect(clib_parity_domain_rule_count("simpleos")).to_be_greater_than(0)
```

</details>

### clib_parity_rule_table

#### AC-3: returns at least 3 rules

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = clib_parity_rule_table()

val count = rules.len()
expect(count).to_be_greater_than(2)
```

</details>

#### AC-3: first rule has a non-empty name

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = clib_parity_rule_table()
val first_rule = rules[0]

val name_len = first_rule.name.len()
expect(name_len).to_be_greater_than(0)
```

</details>

#### AC-3: rules cover all three pattern kinds

<details>
<summary>Executable SPipe</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = clib_parity_rule_table()

# Check that at least one rule exists for each pattern kind
var has_byte_copy = false
var has_endian = false
var has_checksum = false
var has_filesystem = false
var has_database = false
var has_webserver = false
var has_simpleos = false

var i = 0
while i < rules.len():
    val rule = rules[i]
    if rule.pattern_kind == CLibPatternKind.ByteCopy:
        has_byte_copy = true
    if rule.pattern_kind == CLibPatternKind.EndianLoad:
        has_endian = true
    if rule.pattern_kind == CLibPatternKind.ChecksumReducer:
        has_checksum = true
    if rule.domain == "filesystem":
        has_filesystem = true
    if rule.domain == "database":
        has_database = true
    if rule.domain == "webserver":
        has_webserver = true
    if rule.domain == "simpleos":
        has_simpleos = true
    i = i + 1

expect(has_byte_copy).to_equal(true)
expect(has_endian).to_equal(true)
expect(has_checksum).to_equal(true)
expect(has_filesystem).to_equal(true)
expect(has_database).to_equal(true)
expect(has_webserver).to_equal(true)
expect(has_simpleos).to_equal(true)
```

</details>

#### keeps provider rules general rather than optimizer-only

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clib_parity_all_rules_are_general()).to_equal(true)
expect(clib_parity_domain_rule_count("filesystem")).to_be_greater_than(2)
expect(clib_parity_domain_rule_count("database")).to_be_greater_than(14)
expect(clib_parity_domain_rule_count("webserver")).to_be_greater_than(1)
expect(clib_parity_domain_rule_count("simpleos")).to_be_greater_than(2)
```

</details>

#### requires explicit proofs for filesystem, DB, web, and SimpleOS rewrites

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = clib_parity_rule_table()
var all_have_proofs = true
var i = 0
while i < rules.len():
    if rules[i].required_proof == "":
        all_have_proofs = false
    i = i + 1
expect(all_have_proofs).to_equal(true)
```

</details>

#### marks SimpleOS/QEMU rules safe only when ordering or fail-closed contracts are preserved

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = clib_parity_rule_table()
var simpleos_safe = true
var i = 0
while i < rules.len():
    if rules[i].domain == "simpleos" and not clib_parity_rule_is_simpleos_safe(rules[i]):
        simpleos_safe = false
    i = i + 1
expect(simpleos_safe).to_equal(true)
```

</details>

#### gates bounded MMIO polling on volatile ordering proof

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_mmio_poll_loop")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(clib_parity_rule_can_rewrite(rule, ["volatile_mmio"], [])).to_equal(false)
    val decision = clib_parity_rule_rewrite_decision(rule, ["volatile_mmio"], ["volatile_ordering_preserved"])
    expect(decision.eligible).to_equal(true)
    expect(decision.intrinsic).to_equal("hal_mmio_poll_bounded")
```

</details>

#### gates serial marker scanning on marker contract proof

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_serial_marker_scan")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val missing_fact = clib_parity_rule_rewrite_decision(rule, [], ["marker_contract_preserved"])
    expect(missing_fact.eligible).to_equal(false)
    expect(missing_fact.reason).to_equal("missing_required_fact:bounded_serial")
    val decision = clib_parity_rule_rewrite_decision(rule, ["bounded_serial"], ["marker_contract_preserved"])
    expect(decision.eligible).to_equal(true)
```

</details>

#### gates provider grant checks on fail-closed proof

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_provider_grants")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val missing_proof = clib_parity_rule_rewrite_decision(rule, ["grant_tokens"], ["marker_contract_preserved"])
    expect(missing_proof.eligible).to_equal(false)
    expect(missing_proof.reason).to_equal("missing_required_proof:fail_closed_equivalence")
    val decision = clib_parity_rule_rewrite_decision(rule, ["grant_tokens"], ["fail_closed_equivalence"])
    expect(decision.eligible).to_equal(true)
```

</details>

#### uses the same proof gate for filesystem, database, and webserver rules

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs_rule = clib_parity_rule_by_name("match_fat_dir_scan")
val db_rule = clib_parity_rule_by_name("match_db_prefix_lookup")
val web_rule = clib_parity_rule_by_name("match_http_header_scan")

expect(fs_rule.?).to_equal(true)
expect(db_rule.?).to_equal(true)
expect(web_rule.?).to_equal(true)

if fs_rule:
    expect(clib_parity_rule_can_rewrite(fs_rule.unwrap(), ["fat_dir_entry"], ["directory_order_preserved"])).to_equal(true)
if db_rule:
    expect(clib_parity_rule_can_rewrite(db_rule.unwrap(), ["prefix_index"], ["index_update_delete_drop"])).to_equal(true)
if web_rule:
    expect(clib_parity_rule_can_rewrite(web_rule.unwrap(), ["bounded_headers"], ["parser_limit_equivalence"])).to_equal(true)
```

</details>

### clib_parity_rule_provider

#### AC-3: returns provider with required_facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = clib_parity_rule_provider()

val facts = provider.required_facts
expect(facts).to_contain("typed_mir")
expect(facts).to_contain("loop_bounds_proof")
expect(facts).to_contain("semantic_equivalence_proof")
expect(facts).to_contain("provider_boundary_proof")
```

</details>

#### AC-3: returns provider with produced_facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = clib_parity_rule_provider()

val facts = provider.produced_facts
expect(facts).to_contain("clib_parity_rewrite")
expect(facts).to_contain("general_hotpath_rewrite")
expect(facts).to_contain("provider_boundary_preserved")
```

</details>

#### AC-3: provider safety class is pure

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = clib_parity_rule_provider()

expect(provider.safety_class).to_equal("pure")
```

</details>

### DB optimization CLibPatternKind variants (AC-5)

#### AC-5: enum has FtsMatch variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.FtsMatch
val is_fts = kind == CLibPatternKind.FtsMatch
expect(is_fts).to_equal(true)
```

</details>

#### AC-5: enum has ContainsSearch variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.ContainsSearch
val is_contains = kind == CLibPatternKind.ContainsSearch
expect(is_contains).to_equal(true)
```

</details>

#### AC-5: enum has PageSummaryScan variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.PageSummaryScan
val is_page = kind == CLibPatternKind.PageSummaryScan
expect(is_page).to_equal(true)
```

</details>

#### AC-5: enum has CacheInvalidation variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.CacheInvalidation
val is_cache = kind == CLibPatternKind.CacheInvalidation
expect(is_cache).to_equal(true)
```

</details>

#### AC-5: enum has ReopenRecovery variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.ReopenRecovery
val is_reopen = kind == CLibPatternKind.ReopenRecovery
expect(is_reopen).to_equal(true)
```

</details>

### DB optimization rules in clib_parity_rule_table (AC-5)

#### AC-5: database domain has at least 12 rules after DB hardening

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clib_parity_domain_rule_count("database")).to_be_greater_than(14)
```

</details>

#### AC-5: match_db_fts_match rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_fts_match")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.intrinsic).to_equal("db_fts_match")
    expect(rule.required_fact).to_equal("fts_index")
    expect(rule.required_proof).to_equal("fts_index_consistency")
    expect(rule.domain).to_equal("database")
```

</details>

#### AC-5: match_db_contains_search rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_contains_search")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.intrinsic).to_equal("db_contains_search")
    expect(rule.required_fact).to_equal("text_index")
    expect(rule.required_proof).to_equal("text_index_consistency")
    expect(rule.domain).to_equal("database")
```

</details>

#### AC-5: match_db_page_summary_scan rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_page_summary_scan")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.intrinsic).to_equal("db_page_summary_scan")
    expect(rule.required_fact).to_equal("page_summary_index")
    expect(rule.required_proof).to_equal("summary_range_soundness")
    expect(rule.domain).to_equal("database")
```

</details>

#### AC-5: match_db_cache_invalidate rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_cache_invalidate")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.intrinsic).to_equal("db_cache_invalidate")
    expect(rule.required_fact).to_equal("fts_dirty_flag")
    expect(rule.required_proof).to_equal("mutation_invalidation_complete")
    expect(rule.domain).to_equal("database")
```

</details>

#### AC-5: match_db_reopen_recovery rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_reopen_recovery")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.intrinsic).to_equal("db_reopen_recovery")
    expect(rule.required_fact).to_equal("wal_log")
    expect(rule.required_proof).to_equal("wal_replay_idempotent")
    expect(rule.domain).to_equal("database")
```

</details>

### DB optimization rewrite decisions (AC-5)

#### AC-5: FTS match rewrite gated on fts_index fact and fts_index_consistency proof

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_fts_match")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val no_fact = clib_parity_rule_rewrite_decision(rule, [], ["fts_index_consistency"])
    expect(no_fact.eligible).to_equal(false)
    expect(no_fact.reason).to_equal("missing_required_fact:fts_index")
    val no_proof = clib_parity_rule_rewrite_decision(rule, ["fts_index"], [])
    expect(no_proof.eligible).to_equal(false)
    expect(no_proof.reason).to_equal("missing_required_proof:fts_index_consistency")
    val ok = clib_parity_rule_rewrite_decision(rule, ["fts_index"], ["fts_index_consistency"])
    expect(ok.eligible).to_equal(true)
    expect(ok.intrinsic).to_equal("db_fts_match")
```

</details>

#### AC-5: contains search rewrite gated on text_index and text_index_consistency

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_contains_search")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val missing = clib_parity_rule_rewrite_decision(rule, [], [])
    expect(missing.eligible).to_equal(false)
    val ok = clib_parity_rule_rewrite_decision(rule, ["text_index"], ["text_index_consistency"])
    expect(ok.eligible).to_equal(true)
```

</details>

#### AC-5: page summary scan rewrite gated on page_summary_index and summary_range_soundness

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_page_summary_scan")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val missing = clib_parity_rule_rewrite_decision(rule, [], [])
    expect(missing.eligible).to_equal(false)
    val ok = clib_parity_rule_rewrite_decision(rule, ["page_summary_index"], ["summary_range_soundness"])
    expect(ok.eligible).to_equal(true)
```

</details>

#### AC-5: cache invalidation rewrite gated on fts_dirty_flag and mutation_invalidation_complete

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_cache_invalidate")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val missing = clib_parity_rule_rewrite_decision(rule, [], [])
    expect(missing.eligible).to_equal(false)
    val ok = clib_parity_rule_rewrite_decision(rule, ["fts_dirty_flag"], ["mutation_invalidation_complete"])
    expect(ok.eligible).to_equal(true)
```

</details>

#### AC-5: reopen recovery rewrite gated on wal_log and wal_replay_idempotent

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_reopen_recovery")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val missing = clib_parity_rule_rewrite_decision(rule, [], [])
    expect(missing.eligible).to_equal(false)
    val ok = clib_parity_rule_rewrite_decision(rule, ["wal_log"], ["wal_replay_idempotent"])
    expect(ok.eligible).to_equal(true)
```

</details>

### New CLibPatternKind variants (AC-8)

#### AC-8: enum has DictLookupFusion variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.DictLookupFusion
val is_dict = kind == CLibPatternKind.DictLookupFusion
expect(is_dict).to_equal(true)
```

</details>

#### AC-8: enum has ArrayLenHoist variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.ArrayLenHoist
val is_hoist = kind == CLibPatternKind.ArrayLenHoist
expect(is_hoist).to_equal(true)
```

</details>

#### AC-8: enum has DeadBranchElim variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.DeadBranchElim
val is_dead = kind == CLibPatternKind.DeadBranchElim
expect(is_dead).to_equal(true)
```

</details>

#### AC-8: enum has StringConcatReduce variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.StringConcatReduce
val is_concat = kind == CLibPatternKind.StringConcatReduce
expect(is_concat).to_equal(true)
```

</details>

#### AC-8: enum has IntCmpStrengthReduce variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.IntCmpStrengthReduce
val is_cmp = kind == CLibPatternKind.IntCmpStrengthReduce
expect(is_cmp).to_equal(true)
```

</details>

### Dict lookup fusion rules (AC-8)

#### AC-8: match_db_dict_lookup_fusion rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_dict_lookup_fusion")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val is_dict = rule.pattern_kind == CLibPatternKind.DictLookupFusion
    expect(is_dict).to_equal(true)
    expect(rule.intrinsic).to_equal("db_dict_lookup_fused")
    expect(rule.required_fact).to_equal("hash_index")
    expect(rule.required_proof).to_equal("key_immutable_in_sequence")
    expect(rule.domain).to_equal("database")
    expect(rule.cost_delta).to_equal(-5)
    expect(rule.software_cost).to_equal(1400)
```

</details>

#### AC-8: dict lookup fusion rewrite gated on hash_index and key_immutable_in_sequence

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_dict_lookup_fusion")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val no_fact = clib_parity_rule_rewrite_decision(rule, [], ["key_immutable_in_sequence"])
    expect(no_fact.eligible).to_equal(false)
    expect(no_fact.reason).to_equal("missing_required_fact:hash_index")
    val no_proof = clib_parity_rule_rewrite_decision(rule, ["hash_index"], [])
    expect(no_proof.eligible).to_equal(false)
    expect(no_proof.reason).to_equal("missing_required_proof:key_immutable_in_sequence")
    val ok = clib_parity_rule_rewrite_decision(rule, ["hash_index"], ["key_immutable_in_sequence"])
    expect(ok.eligible).to_equal(true)
```

</details>

#### AC-8: general dict lookup fusion rule exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_general_dict_lookup_fusion")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.domain).to_equal("general")
    expect(rule.intrinsic).to_equal("dict_lookup_fused")
```

</details>

### Array length hoisting rules (AC-8)

#### AC-8: match_db_array_len_hoist rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_array_len_hoist")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val is_hoist = rule.pattern_kind == CLibPatternKind.ArrayLenHoist
    expect(is_hoist).to_equal(true)
    expect(rule.intrinsic).to_equal("db_array_len_hoisted")
    expect(rule.required_fact).to_equal("loop_invariant")
    expect(rule.required_proof).to_equal("array_no_mutation_in_loop")
    expect(rule.domain).to_equal("database")
    expect(rule.cost_delta).to_equal(-4)
```

</details>

<details>
<summary>Advanced: AC-8: array len hoist rewrite gated on loop_invariant and array_no_mutation_in_loop</summary>

#### AC-8: array len hoist rewrite gated on loop_invariant and array_no_mutation_in_loop

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_array_len_hoist")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val missing = clib_parity_rule_rewrite_decision(rule, [], [])
    expect(missing.eligible).to_equal(false)
    val ok = clib_parity_rule_rewrite_decision(rule, ["loop_invariant"], ["array_no_mutation_in_loop"])
    expect(ok.eligible).to_equal(true)
```

</details>


</details>

#### AC-8: general array len hoist rule exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_general_array_len_hoist")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.domain).to_equal("general")
    expect(rule.intrinsic).to_equal("array_len_hoisted")
```

</details>

### Dead branch elimination rules (AC-8)

#### AC-8: match_db_dead_branch_elim rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_dead_branch_elim")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val is_dead = rule.pattern_kind == CLibPatternKind.DeadBranchElim
    expect(is_dead).to_equal(true)
    expect(rule.intrinsic).to_equal("db_dead_branch_removed")
    expect(rule.required_fact).to_equal("const_condition")
    expect(rule.required_proof).to_equal("branch_condition_is_const")
    expect(rule.domain).to_equal("database")
    expect(rule.cost_delta).to_equal(-3)
```

</details>

#### AC-8: dead branch elim rewrite gated on const_condition and branch_condition_is_const

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_dead_branch_elim")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val missing = clib_parity_rule_rewrite_decision(rule, [], [])
    expect(missing.eligible).to_equal(false)
    val ok = clib_parity_rule_rewrite_decision(rule, ["const_condition"], ["branch_condition_is_const"])
    expect(ok.eligible).to_equal(true)
```

</details>

#### AC-8: general dead branch elim rule exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_general_dead_branch_elim")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.domain).to_equal("general")
    expect(rule.intrinsic).to_equal("dead_branch_removed")
```

</details>

### String concat reduction rules (AC-8)

#### AC-8: match_db_string_concat_reduce rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_string_concat_reduce")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val is_concat = rule.pattern_kind == CLibPatternKind.StringConcatReduce
    expect(is_concat).to_equal(true)
    expect(rule.intrinsic).to_equal("db_string_concat_batch")
    expect(rule.required_fact).to_equal("string_builder")
    expect(rule.required_proof).to_equal("concat_order_preserved")
    expect(rule.domain).to_equal("database")
    expect(rule.cost_delta).to_equal(-6)
    expect(rule.software_cost).to_equal(1500)
```

</details>

#### AC-8: string concat reduce rewrite gated on string_builder and concat_order_preserved

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_string_concat_reduce")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val no_fact = clib_parity_rule_rewrite_decision(rule, [], ["concat_order_preserved"])
    expect(no_fact.eligible).to_equal(false)
    expect(no_fact.reason).to_equal("missing_required_fact:string_builder")
    val ok = clib_parity_rule_rewrite_decision(rule, ["string_builder"], ["concat_order_preserved"])
    expect(ok.eligible).to_equal(true)
```

</details>

#### AC-8: general string concat reduce rule exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_general_string_concat_reduce")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.domain).to_equal("general")
    expect(rule.intrinsic).to_equal("string_concat_batch")
```

</details>

### Integer comparison strength reduction rules (AC-8)

#### AC-8: match_db_int_cmp_strength rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_int_cmp_strength")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val is_cmp = rule.pattern_kind == CLibPatternKind.IntCmpStrengthReduce
    expect(is_cmp).to_equal(true)
    expect(rule.intrinsic).to_equal("db_int_cmp_reduced")
    expect(rule.required_fact).to_equal("none")
    expect(rule.required_proof).to_equal("comparison_semantics_preserved")
    expect(rule.domain).to_equal("database")
    expect(rule.cost_delta).to_equal(-3)
    expect(rule.software_cost).to_equal(800)
```

</details>

#### AC-8: int cmp strength reduce needs only proof, no fact (requires=none)

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_int_cmp_strength")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val no_proof = clib_parity_rule_rewrite_decision(rule, [], [])
    expect(no_proof.eligible).to_equal(false)
    expect(no_proof.reason).to_equal("missing_required_proof:comparison_semantics_preserved")
    val ok = clib_parity_rule_rewrite_decision(rule, [], ["comparison_semantics_preserved"])
    expect(ok.eligible).to_equal(true)
```

</details>

#### AC-8: general int cmp strength reduce rule exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_general_int_cmp_strength")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.domain).to_equal("general")
    expect(rule.intrinsic).to_equal("int_cmp_reduced")
    expect(rule.software_cost).to_equal(700)
```

</details>

### New CLibPatternKind variants (AC-9)

#### AC-9: enum has ScanResultCache variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.ScanResultCache
val is_scan = kind == CLibPatternKind.ScanResultCache
expect(is_scan).to_equal(true)
```

</details>

#### AC-9: enum has VisibilityBatchPrecompute variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.VisibilityBatchPrecompute
val is_vis = kind == CLibPatternKind.VisibilityBatchPrecompute
expect(is_vis).to_equal(true)
```

</details>

#### AC-9: enum has CopyElisionPointLookup variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.CopyElisionPointLookup
val is_pt = kind == CLibPatternKind.CopyElisionPointLookup
expect(is_pt).to_equal(true)
```

</details>

### Scan result cache rules (AC-9)

#### AC-9: match_db_scan_result_cache rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_scan_result_cache")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val is_scan = rule.pattern_kind == CLibPatternKind.ScanResultCache
    expect(is_scan).to_equal(true)
    expect(rule.domain).to_equal("database")
    expect(rule.intrinsic).to_equal("db_scan_result_cached")
    expect(rule.required_fact).to_equal("scan_cache_key")
    expect(rule.required_proof).to_equal("mutation_invalidation_complete")
    expect(rule.cost_delta).to_equal(-8)
```

</details>

#### AC-9: match_general_scan_result_cache rule exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_general_scan_result_cache")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.domain).to_equal("general")
    expect(rule.intrinsic).to_equal("scan_result_cached")
    expect(rule.software_cost).to_equal(1800)
```

</details>

#### AC-9: scan cache rewrite gated on scan_cache_key and mutation_invalidation_complete

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_scan_result_cache")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val missing = clib_parity_rule_rewrite_decision(rule, [], [])
    expect(missing.eligible).to_equal(false)
    val ok = clib_parity_rule_rewrite_decision(rule, ["scan_cache_key"], ["mutation_invalidation_complete"])
    expect(ok.eligible).to_equal(true)
```

</details>

### Visibility batch precompute rules (AC-9)

#### AC-9: match_db_visibility_batch rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_visibility_batch")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val is_vis = rule.pattern_kind == CLibPatternKind.VisibilityBatchPrecompute
    expect(is_vis).to_equal(true)
    expect(rule.domain).to_equal("database")
    expect(rule.intrinsic).to_equal("db_vis_batch_precomputed")
    expect(rule.required_fact).to_equal("snapshot_epoch")
    expect(rule.required_proof).to_equal("snapshot_monotonic_equivalence")
```

</details>

#### AC-9: match_general_filter_batch rule exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_general_filter_batch")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.domain).to_equal("general")
    expect(rule.intrinsic).to_equal("filter_batch_precomputed")
```

</details>

### Copy elision point lookup rules (AC-9)

#### AC-9: match_db_pk_point_lookup rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_pk_point_lookup")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val is_pt = rule.pattern_kind == CLibPatternKind.CopyElisionPointLookup
    expect(is_pt).to_equal(true)
    expect(rule.domain).to_equal("database")
    expect(rule.intrinsic).to_equal("db_pk_point_lookup_direct")
    expect(rule.required_fact).to_equal("pk_index")
    expect(rule.required_proof).to_equal("index_key_immutable_in_lookup")
    expect(rule.cost_delta).to_equal(-7)
```

</details>

#### AC-9: match_general_index_point_lookup rule exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_general_index_point_lookup")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.domain).to_equal("general")
    expect(rule.intrinsic).to_equal("index_point_lookup_direct")
    expect(rule.software_cost).to_equal(1400)
```

</details>

#### AC-9: pk point lookup rewrite gated on pk_index and index_key_immutable_in_lookup

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_pk_point_lookup")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val missing = clib_parity_rule_rewrite_decision(rule, [], [])
    expect(missing.eligible).to_equal(false)
    val ok = clib_parity_rule_rewrite_decision(rule, ["pk_index"], ["index_key_immutable_in_lookup"])
    expect(ok.eligible).to_equal(true)
```

</details>

### Flat key index rules (AC-10)

#### AC-10: enum has FlatKeyIndex variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CLibPatternKind.FlatKeyIndex
val is_fk = kind == CLibPatternKind.FlatKeyIndex
expect(is_fk).to_equal(true)
```

</details>

#### AC-10: match_db_flat_key_index rule exists with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_flat_key_index")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val is_fk = rule.pattern_kind == CLibPatternKind.FlatKeyIndex
    expect(is_fk).to_equal(true)
    expect(rule.domain).to_equal("database")
    expect(rule.intrinsic).to_equal("db_flat_key_lookup")
    expect(rule.required_fact).to_equal("flat_key_dict")
    expect(rule.required_proof).to_equal("composite_key_bijective")
    expect(rule.cost_delta).to_equal(-8)
```

</details>

#### AC-10: match_general_flat_key_index rule exists

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_general_flat_key_index")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    expect(rule.domain).to_equal("general")
    expect(rule.intrinsic).to_equal("flat_key_lookup")
    expect(rule.software_cost).to_equal(1600)
```

</details>

#### AC-10: flat key rewrite gated on flat_key_dict and composite_key_bijective

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_rule = clib_parity_rule_by_name("match_db_flat_key_index")
expect(maybe_rule.?).to_equal(true)
if maybe_rule:
    val rule = maybe_rule.unwrap()
    val missing = clib_parity_rule_rewrite_decision(rule, [], [])
    expect(missing.eligible).to_equal(false)
    val ok = clib_parity_rule_rewrite_decision(rule, ["flat_key_dict"], ["composite_key_bijective"])
    expect(ok.eligible).to_equal(true)
```

</details>

### optimization_rule_provider_clib_parity factory

#### AC-3: factory creates provider with given name

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = optimization_rule_provider_clib_parity("test_clib", true)

expect(provider.name).to_equal("test_clib")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 70 |
| Active scenarios | 70 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/pure_simple_lib_standalone_hw_plan.md](doc/03_plan/pure_simple_lib_standalone_hw_plan.md)


</details>

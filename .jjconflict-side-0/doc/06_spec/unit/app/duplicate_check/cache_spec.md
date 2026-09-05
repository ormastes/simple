# Cache Specification

> Tests covering TokenCacheManager creation, File modification time, Token caching, Cache operations, Cache statistics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cache Specification

## Scenarios

### TokenCacheManager creation

#### creates empty cache manager

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates empty cache manager


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty cache manager")
val manager = new_token_cache_manager()
val stats = get_cache_stats(manager)
expect(stats).to_contain("0 files")
```

</details>

### File modification time

#### gets mtime for existing file

- gets mtime for existing file


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets mtime for existing file")
val test_file = "/tmp/test_cache_mtime.txt"
create_test_file(test_file, "test content")

val mtime = get_file_mtime(test_file)
expect(mtime).to_be_greater_than(0)

delete_test_file(test_file)
```

</details>

#### returns 0 for non-existent file

- returns 0 for non-existent file
   - Expected: mtime equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for non-existent file")
val mtime = get_file_mtime("/tmp/nonexistent_file_xyz.txt")
expect(mtime).to_equal(0)
```

</details>

### Token caching

#### caches tokens on first access

- caches tokens on first access
   - Expected: tokens1.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches tokens on first access")
val manager = new_token_cache_manager()
val test_file = "/tmp/test_cache_tokens.spl"
create_test_file(test_file, "fn test(): 42")

fn tokenize_fn(path: text) -> [SimpleToken]:
    create_sample_tokens()

val tokens1 = get_tokens_cached(manager, test_file, tokenize_fn)
expect(tokens1.len()).to_equal(2)
expect(get_cache_stats(manager)).to_contain("1 files")

delete_test_file(test_file)
```

</details>

#### returns cached tokens without re-tokenizing

- returns cached tokens without re-tokenizing
   - Expected: tokens1.len() equals `tokens2.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns cached tokens without re-tokenizing")
val manager = new_token_cache_manager()
val test_file = "/tmp/test_cache_reuse.spl"
create_test_file(test_file, "fn test(): 42")

fn tokenize_fn(path: text) -> [SimpleToken]:
    create_sample_tokens()

val tokens1 = get_tokens_cached(manager, test_file, tokenize_fn)
val tokens2 = get_tokens_cached(manager, test_file, tokenize_fn)

expect(tokens1.len()).to_equal(tokens2.len())
expect(get_cache_stats(manager)).to_contain("1 files")

delete_test_file(test_file)
```

</details>

#### invalidates cache when file changes

- invalidates cache when file changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates cache when file changes")
val manager = new_token_cache_manager()
val test_file = "/tmp/test_cache_invalidate.spl"

create_test_file(test_file, "fn test(): 42")

fn tokenize_fn(path: text) -> [SimpleToken]:
    val content = shell("cat '{path}'").stdout.trim()
    [
        SimpleToken(kind: SimpleTokenKind.Keyword, value: "fn", line: 1, column: 1, start_offset: 0, end_offset: 2),
        SimpleToken(kind: SimpleTokenKind.Identifier, value: content, line: 1, column: 4, start_offset: 3, end_offset: 3 + content.len())
    ]

val tokens1 = get_tokens_cached(manager, test_file, tokenize_fn)

create_test_file(test_file, "fn test(): 99")

val tokens2 = get_tokens_cached(manager, test_file, tokenize_fn)

expect(tokens1[1].value).to_not_equal(tokens2[1].value)

delete_test_file(test_file)
```

</details>

### Cache operations

#### invalidates specific file

- invalidates specific file


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates specific file")
val manager = new_token_cache_manager()
val test_file1 = "/tmp/test_cache_inv1.spl"
val test_file2 = "/tmp/test_cache_inv2.spl"

create_test_file(test_file1, "fn test1(): 1")
create_test_file(test_file2, "fn test2(): 2")

fn tokenize_fn(path: text) -> [SimpleToken]:
    create_sample_tokens()

val tokens1 = get_tokens_cached(manager, test_file1, tokenize_fn)
val tokens2 = get_tokens_cached(manager, test_file2, tokenize_fn)

val stats_before = get_cache_stats(manager)
expect(stats_before).to_contain("2 files")

invalidate_file(manager, test_file1)

val stats_after = get_cache_stats(manager)
expect(stats_after).to_contain("1 files")

delete_test_file(test_file1)
delete_test_file(test_file2)
```

</details>

#### clears all cache entries

- clears all cache entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all cache entries")
val manager = new_token_cache_manager()
val test_file = "/tmp/test_cache_clear.spl"

create_test_file(test_file, "fn test(): 42")

fn tokenize_fn(path: text) -> [SimpleToken]:
    create_sample_tokens()

val tokens = get_tokens_cached(manager, test_file, tokenize_fn)

val stats_before = get_cache_stats(manager)
expect(stats_before).to_contain("1 files")

clear_cache(manager)

val stats_after = get_cache_stats(manager)
expect(stats_after).to_contain("0 files")

delete_test_file(test_file)
```

</details>

### Cache statistics

#### reports correct token count

- reports correct token count


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports correct token count")
val manager = new_token_cache_manager()
val test_file = "/tmp/test_cache_stats.spl"

create_test_file(test_file, "fn test(): 42")

fn tokenize_fn(path: text) -> [SimpleToken]:
    create_sample_tokens()

val tokens = get_tokens_cached(manager, test_file, tokenize_fn)

val stats = get_cache_stats(manager)
expect(stats).to_contain("1 files")
expect(stats).to_contain("2 tokens")

delete_test_file(test_file)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/duplicate_check/cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TokenCacheManager creation, File modification time, Token caching, Cache operations, Cache statistics.
- TokenCacheManager creation
- File modification time
- Token caching
- Cache operations
- Cache statistics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `24132c036ee864c4d916c32b0bd7f483effe99fa5b926ccf490219acbc62f4a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24132c036ee864c4d916c32b0bd7f483effe99fa5b926ccf490219acbc62f4a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24132c036ee864c4d916c32b0bd7f483effe99fa5b926ccf490219acbc62f4a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/duplicate_check/cache_spec.spl
mirror: doc/06_spec/unit/app/duplicate_check/cache_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/duplicate_check/cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/duplicate_check/cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/duplicate_check/cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/duplicate_check/cache_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty cache manager' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/duplicate_check/cache_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets mtime for existing file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/duplicate_check/cache_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 for non-existent file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Cache Specification

> <details>

<!-- sdn-diagram:id=cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cache_spec -> compiler
cache_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cache Specification

## Scenarios

### TokenCacheManager creation

#### creates empty cache manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manager = new_token_cache_manager()
val stats = get_cache_stats(manager)
expect(stats).to_contain("0 files")
```

</details>

### File modification time

#### gets mtime for existing file

1. create test file
2. delete test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_cache_mtime.txt"
create_test_file(test_file, "test content")

val mtime = get_file_mtime(test_file)
expect(mtime).to_be_greater_than(0)

delete_test_file(test_file)
```

</details>

#### returns 0 for non-existent file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mtime = get_file_mtime("/tmp/nonexistent_file_xyz.txt")
expect(mtime).to_equal(0)
```

</details>

### Token caching

#### caches tokens on first access

1. create test file
2. fn tokenize fn
3. create sample tokens
   - Expected: tokens1.len() equals `2`
4. delete test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. create test file
2. fn tokenize fn
3. create sample tokens
   - Expected: tokens1.len() equals `tokens2.len()`
4. delete test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. create test file
2. fn tokenize fn
3. SimpleToken
4. SimpleToken
5. create test file
   - Expected: tokens1[1].value == tokens2[1].value is false
6. delete test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

expect(tokens1[1].value == tokens2[1].value).to_equal(false)

delete_test_file(test_file)
```

</details>

### Cache operations

#### invalidates specific file

1. create test file
2. create test file
3. fn tokenize fn
4. create sample tokens
5. invalidate file
6. delete test file
7. delete test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. create test file
2. fn tokenize fn
3. create sample tokens
4. clear cache
5. delete test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. create test file
2. fn tokenize fn
3. create sample tokens
4. delete test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/duplicate_check/cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

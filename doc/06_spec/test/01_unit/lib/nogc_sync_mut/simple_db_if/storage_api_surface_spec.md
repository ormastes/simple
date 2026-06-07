# Storage API Trait Surface Completion Specification

> Verifies that the storage_api.spl trait definitions include all required

<!-- sdn-diagram:id=storage_api_surface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=storage_api_surface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

storage_api_surface_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=storage_api_surface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage API Trait Surface Completion Specification

Verifies that the storage_api.spl trait definitions include all required

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Failing (no implementation yet) |
| Source | `test/01_unit/lib/nogc_sync_mut/simple_db_if/storage_api_surface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**ACs:** AC-3 (trait surface audit), AC-5 (hardening fix), AC-7 (new tests)
Verifies that the storage_api.spl trait definitions include all required
method signatures by writing mock impl blocks. If a method is missing
from the trait, the impl block fails to compile and the spec file fails
to load — which is the red-phase TDD signal.

## Scenarios

### WalWriter trait

#### wal_group_commit is callable and returns Lsn

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = make_mock_wal()
val result = require_wal_group_commit(w, Lsn(value: 42))
expect(result.value).to_equal(42)
```

</details>

### BufferManager trait

#### buf_release is callable and returns bool

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bm = make_mock_buf()
val page = PageBuf(arena_id: 1, offset: 0, length: 4096, generation: 1)
val result = require_buf_release(bm, page)
expect(result).to_equal(true)
```

</details>

#### buf_pin_count is callable and returns i64

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bm = make_mock_buf()
val count = require_buf_pin_count(bm, Rel(id: 1), BlkNo(n: 0))
expect(count).to_equal(0)
```

</details>

### PageStore trait

#### page_read is callable and returns byte array

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ps = make_mock_pages()
val data = require_page_read(ps, Rel(id: 1), BlkNo(n: 0))
expect(data.len()).to_equal(0)
```

</details>

### Checkpointer trait

#### checkpoint_commit returns Result not bool

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ck = make_mock_ckpt()
val result = require_checkpoint_commit(ck, Lsn(value: 100))
# If checkpoint_commit still returns bool, .is_ok() won't exist
expect(result.is_ok()).to_equal(true)
val lsn = result.unwrap()
expect(lsn.value).to_equal(100)
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

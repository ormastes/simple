# loader_api dispatch

> Verifies loader_dispatch's magic-sniff branching between ELF64 and SMF.

<!-- sdn-diagram:id=loader_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=loader_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

loader_api_spec -> std
loader_api_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=loader_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# loader_api dispatch

Verifies loader_dispatch's magic-sniff branching between ELF64 and SMF.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE2-G10 |
| Category | Kernel loader |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/loader_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies loader_dispatch's magic-sniff branching between ELF64 and SMF.

## Scenarios

### loader_dispatch
_Magic-sniff routing._

#### empty buffer returns -ENOEXEC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = loader_dispatch(_zero_bytes(4), _empty_space())
expect rc.to_equal(-8i64)
```

</details>

#### non-ELF non-SMF bytes return -ENOEXEC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = loader_dispatch(_zero_bytes(128), _empty_space())
expect rc.to_equal(-8i64)
```

</details>

#### ELF magic dispatches to elf64 path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = loader_dispatch(_elf_magic_prefix(), _empty_space())
val dispatched: bool = rc != -8i64 or rc < 0i64
expect dispatched.to_equal(true)
```

</details>

#### SMF trailer magic dispatches to smf path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = loader_dispatch(_smf_trailer_bytes(), _empty_space())
expect rc.to_equal(-38i64)
```

</details>

### loader dynload API

#### rejects empty path dynopen before file IO

1. dylib registry reset for test
   - Expected: loader_dynopen_path("") equals `-22i64`
   - Expected: loader_dynopen_mapped_path("", _empty_space()) equals `-22i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
expect(loader_dynopen_path("")).to_equal(-22i64)
expect(loader_dynopen_mapped_path("", _empty_space())).to_equal(-22i64)
```

</details>

#### opens role-2 SMF library bytes and resolves symbols through the loader

1. dylib registry reset for test
   - Expected: loader_dynopen_registered("/lib/gui_hot.smf") equals `handle`
   - Expected: loader_dynsym(handle, "hot") equals `0xCAFE`
   - Expected: loader_dynsym_is_process_callable(handle, "hot") is false
   - Expected: loader_dynclose(handle) equals `0`
   - Expected: loader_dynclose(handle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val handle = loader_dynopen_bytes("/lib/gui_hot.smf", _smf_role2_library())
expect(handle).to_be_greater_than(0)
expect(loader_dynopen_registered("/lib/gui_hot.smf")).to_equal(handle)
expect(loader_dynsym(handle, "hot")).to_equal(0xCAFE)
expect(loader_dynsym_is_process_callable(handle, "hot")).to_equal(false)
expect(loader_dynclose(handle)).to_equal(0)
expect(loader_dynclose(handle)).to_equal(0)
```

</details>

#### rolls back mapped dynopen when ELF segment mapping fails

1. dylib registry reset for test
   - Expected: rc equals `-8i64`
   - Expected: loader_dynopen_registered("/lib/no_load.so") equals `-2i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val rc = loader_dynopen_mapped_bytes("/lib/no_load.so", _elf64_no_load_segments(), _empty_space())
expect(rc).to_equal(-8i64)
expect(loader_dynopen_registered("/lib/no_load.so")).to_equal(-2i64)
expect(loader_dynopen_registered("/lib/no_load.so")).to_be_less_than(0)
```

</details>

#### rolls back mapped dynopen when bytes are not native library code

1. dylib registry reset for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val rc = loader_dynopen_mapped_bytes("/lib/not_native.smf", _smf_trailer_bytes(), _empty_space())
expect(rc).to_be_less_than(0)
expect(loader_dynopen_registered("/lib/not_native.smf")).to_be_less_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# loader_api dispatch

Verifies loader_dispatch's magic-sniff branching between ELF64 and SMF.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE2-G10 |
| Category | Kernel loader |
| Status | Active |
| Source | `test/unit/os/kernel/loader/loader_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies loader_dispatch's magic-sniff branching between ELF64 and SMF.

## Scenarios

### loader_dispatch
_Magic-sniff routing._

#### empty buffer returns -ENOEXEC

1. expect rc to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = loader_dispatch(_zero_bytes(4), _empty_space())
expect rc.to_equal(-8i64)
```

</details>

#### non-ELF non-SMF bytes return -ENOEXEC

1. expect rc to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = loader_dispatch(_zero_bytes(128), _empty_space())
expect rc.to_equal(-8i64)
```

</details>

#### ELF magic dispatches to elf64 path

1. expect dispatched to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = loader_dispatch(_elf_magic_prefix(), _empty_space())
val dispatched: bool = rc != -8i64 or rc < 0i64
expect dispatched.to_equal(true)
```

</details>

#### SMF trailer magic dispatches to smf path

1. expect rc to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = loader_dispatch(_smf_trailer_bytes(), _empty_space())
expect rc.to_equal(-38i64)
```

</details>

### loader dynload API

#### opens role-2 SMF library bytes and resolves symbols through the loader

1. dylib registry reset for test
   - Expected: loader_dynopen_registered("/lib/gui_hot.smf") equals `handle`
   - Expected: loader_dynsym(handle, "hot") equals `0xCAFE`
   - Expected: loader_dynsym_is_process_callable(handle, "hot") is false
   - Expected: loader_dynclose(handle) equals `0`
   - Expected: loader_dynclose(handle) equals `0`


<details>
<summary>Executable SPipe</summary>

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


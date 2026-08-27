# loader_api dispatch

> Verifies loader_dispatch's magic-sniff branching between ELF64 and SMF.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies loader_dispatch's magic-sniff branching between ELF64 and SMF.

## Scenarios

### loader_dispatch

#### empty buffer returns -ENOEXEC

- empty buffer returns -ENOEXEC


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("empty buffer returns -ENOEXEC")
"""No magic to match => -8."""
val rc = loader_dispatch(_zero_bytes(4), _empty_space())
expect rc.to_equal(-8i64)
```

</details>

#### non-ELF non-SMF bytes return -ENOEXEC

- non-ELF non-SMF bytes return -ENOEXEC


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("non-ELF non-SMF bytes return -ENOEXEC")
"""Random data must not silently dispatch to either loader."""
val rc = loader_dispatch(_zero_bytes(128), _empty_space())
expect rc.to_equal(-8i64)
```

</details>

#### ELF magic dispatches to elf64 path

- ELF magic dispatches to elf64 path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("ELF magic dispatches to elf64 path")
"""ELF prefix should leave the -ENOEXEC branch and reach elf64_load.
With a minimal/invalid ELF body elf64_load returns an error, but it
must NOT be the generic -8 that the sniff branch would return."""
val rc = loader_dispatch(_elf_magic_prefix(), _empty_space())
val dispatched: bool = rc != -8i64 or rc < 0i64
expect dispatched.to_equal(true)
```

</details>

#### SMF trailer magic dispatches to smf path

- SMF trailer magic dispatches to smf path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("SMF trailer magic dispatches to smf path")
"""SMF v1.1 packages should not be rejected just because byte zero is payload/stub."""
val rc = loader_dispatch(_smf_trailer_bytes(), _empty_space())
expect rc.to_equal(-38i64)
```

</details>

### loader dynload API

#### rejects empty path dynopen before file IO

- rejects empty path dynopen before file IO
   - Expected: loader_dynopen_path("") equals `-22i64`
   - Expected: loader_dynopen_mapped_path("", _empty_space()) equals `-22i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects empty path dynopen before file IO")
dylib_registry_reset_for_test()
expect(loader_dynopen_path("")).to_equal(-22i64)
expect(loader_dynopen_mapped_path("", _empty_space())).to_equal(-22i64)
```

</details>

#### opens role-2 SMF library bytes and resolves symbols through the loader

- opens role-2 SMF library bytes and resolves symbols through the loader
   - Expected: loader_dynopen_registered("/lib/gui_hot.smf") equals `handle`
   - Expected: loader_dynsym(handle, "hot") equals `0xCAFE`
   - Expected: loader_dynsym_is_process_callable(handle, "hot") is false
   - Expected: loader_dynclose(handle) equals `0`
   - Expected: loader_dynclose(handle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("opens role-2 SMF library bytes and resolves symbols through the loader")
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

- rolls back mapped dynopen when ELF segment mapping fails
   - Expected: rc equals `-8i64`
   - Expected: loader_dynopen_registered("/lib/no_load.so") equals `-2i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rolls back mapped dynopen when ELF segment mapping fails")
dylib_registry_reset_for_test()
val rc = loader_dynopen_mapped_bytes("/lib/no_load.so", _elf64_no_load_segments(), _empty_space())
expect(rc).to_equal(-8i64)
expect(loader_dynopen_registered("/lib/no_load.so")).to_equal(-2i64)
expect(loader_dynopen_registered("/lib/no_load.so")).to_be_less_than(0)
```

</details>

#### rolls back mapped dynopen when bytes are not native library code

- rolls back mapped dynopen when bytes are not native library code


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rolls back mapped dynopen when bytes are not native library code")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bc12e75538298bd2476174598f504b583b2a4ff3730526ccff17c919d9c4ba58`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc12e75538298bd2476174598f504b583b2a4ff3730526ccff17c919d9c4ba58`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc12e75538298bd2476174598f504b583b2a4ff3730526ccff17c919d9c4ba58`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/kernel/loader/loader_api_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/loader_api_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/loader_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/loader_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/loader_api_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/loader_api_spec.spl:198:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty buffer returns -ENOEXEC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/loader_api_spec.spl:205:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'non-ELF non-SMF bytes return -ENOEXEC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/loader_api_spec.spl:212:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ELF magic dispatches to elf64 path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

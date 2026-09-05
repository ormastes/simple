# ELF64 dynamic symbol resolution

> Verifies section header parsing and .dynsym/.symtab symbol lookup

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ELF64 dynamic symbol resolution

Verifies section header parsing and .dynsym/.symtab symbol lookup

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE2-G10-DYNSYM |
| Category | Kernel loader |
| Status | Active |
| Source | `test/unit/os/kernel/loader/elf64_dynsym_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies section header parsing and .dynsym/.symtab symbol lookup
from a minimal hand-crafted ELF64 binary with embedded symbol tables.

## Scenarios

### elf64_has_magic

#### detects ELF magic at offset 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects ELF magic at offset 0
   - Expected: elf64_has_magic(data) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects ELF magic at offset 0")
val data = _make_elf64_with_dynsym()
expect(elf64_has_magic(data)).to_equal(true)
```

</details>

#### rejects non-ELF bytes

- rejects non-ELF bytes
   - Expected: elf64_has_magic(data) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-ELF bytes")
var data: [u8] = []
data.push(0.to_u8())
data.push(0.to_u8())
data.push(0.to_u8())
data.push(0.to_u8())
expect(elf64_has_magic(data)).to_equal(false)
```

</details>

### elf64_parse_section_headers

#### parses section headers from minimal ELF64

- parses section headers from minimal ELF64
   - Expected: shdrs.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses section headers from minimal ELF64")
val data = _make_elf64_with_dynsym()
val hdr_opt = elf64_parse_header(data)
val hdr = hdr_opt.unwrap()
val shdrs = elf64_parse_section_headers(data, hdr)
expect(shdrs.len()).to_equal(3)
```

</details>

#### finds .dynsym section by type

- finds .dynsym section by type
   - Expected: dynsym.sh_type equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds .dynsym section by type")
val data = _make_elf64_with_dynsym()
val hdr = elf64_parse_header(data).unwrap()
val shdrs = elf64_parse_section_headers(data, hdr)
val dynsym_opt = elf64_find_section_by_type(shdrs, 11)
val dynsym = dynsym_opt.unwrap()
expect(dynsym.sh_type).to_equal(11)
```

</details>

### elf64_dynsym_lookup

#### resolves a known symbol from .dynsym

- resolves a known symbol from .dynsym
   - Expected: addr equals `0xDEAD.to_u64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a known symbol from .dynsym")
val data = _make_elf64_with_dynsym()
val hdr = elf64_parse_header(data).unwrap()
val shdrs = elf64_parse_section_headers(data, hdr)
val result = elf64_dynsym_lookup(data, shdrs, "hello")
val addr = result.unwrap()
expect(addr).to_equal(0xDEAD.to_u64())
```

</details>

#### returns nil for an unknown symbol

- returns nil for an unknown symbol
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for an unknown symbol")
val data = _make_elf64_with_dynsym()
val hdr = elf64_parse_header(data).unwrap()
val shdrs = elf64_parse_section_headers(data, hdr)
val result = elf64_dynsym_lookup(data, shdrs, "nonexistent")
expect(result).to_equal(nil)
```

</details>

### elf64_strtab_get

#### extracts NUL-terminated strings from strtab

- extracts NUL-terminated strings from strtab
   - Expected: elf64_strtab_get(strtab, 0) equals ``
   - Expected: elf64_strtab_get(strtab, 1) equals `AB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts NUL-terminated strings from strtab")
var strtab: [u8] = []
strtab.push(0.to_u8())       # index 0: empty
strtab.push(0x41.to_u8())    # index 1: "AB"
strtab.push(0x42.to_u8())
strtab.push(0.to_u8())
expect(elf64_strtab_get(strtab, 0)).to_equal("")
expect(elf64_strtab_get(strtab, 1)).to_equal("AB")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `7fb8a8a9d6aa74706ddd6ea3921e40eec78110367d21923ef4ce1e5c9cdf4828`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7fb8a8a9d6aa74706ddd6ea3921e40eec78110367d21923ef4ce1e5c9cdf4828`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7fb8a8a9d6aa74706ddd6ea3921e40eec78110367d21923ef4ce1e5c9cdf4828`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/kernel/loader/elf64_dynsym_spec.spl
mirror: doc/06_spec/unit/os/kernel/loader/elf64_dynsym_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/loader/elf64_dynsym_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/loader/elf64_dynsym_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/loader/elf64_dynsym_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/loader/elf64_dynsym_spec.spl:240:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects ELF magic at offset 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/elf64_dynsym_spec.spl:246:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-ELF bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/elf64_dynsym_spec.spl:257:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses section headers from minimal ELF64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

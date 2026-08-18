# Frozen Design — SSpec Binary Reference, rt_* Hardening, C-to-Simple Migration (2026-08-18)

Status: research / frozen design (next-research doc, saved verbatim from planning session).

## Final frozen design

The vertically stacked multi-word figure is the default SSpec reference view for every fixed-layout struct.

The earlier alternatives remain available, but they are opt-in. The normal authoring path is only:

```
reference NvmeWriteCommand
```

and a typed comparison is only:

```
expect(actual).to_binary(expected)
```

SSpec infers the registered layout from NvmeWriteCommand and generates the same stacked figure for both the reference manual and expected/actual evidence.

Two semantic rules are critical:

1. Gray means genuinely excluded from comparison: `compare_mask = 0` for those bits under the current test context.
2. Reserved does not mean gray: `reserved_zero`, `reserved_one`, and prohibited encodings remain actively checked.

The official NVMe command-set presentation organizes command-specific dwords in command order and separately describes fields that are reserved versus fields ignored by the controller. That supports a stacked-word default with context-dependent comparison masks rather than treating every reserved-looking field as don't-care.

---

## 1. Compact SSpec surface with no language grammar change

The repo already has parser-friendly macros, SSpec, SPipe, and docgen. The prior modern-SSpec design also calls for ordinary Simple expressions and avoiding new grammar where a library/macro surface suffices.

Use command-style SSpec macros:

```
use std.spec.*

# Global reference: emitted once in the document Reference section.
reference NvmeWriteCommand

describe "NVMe Write command":
    # Local reference: shown here, or linked to the global definition.
    reference NvmeCompletion

    it "encodes the command-specific dwords":
        actual = encode_write(command)

        expect(actual).to_binary(expected)
```

The parser/compiler expansion is equivalent to ordinary calls:

```
reference(NvmeWriteCommand)
describe("NVMe Write command", ...)
expect(actual).to_binary(expected)
```

This gives the Ruby-like compact surface without adding a `reference` production to the core language grammar. Ruby's omitted-parenthesis style is useful as the presentation model, although Simple should implement it through the existing macro system rather than generalizing every function call and inheriting Ruby's call-ambiguity cases.

### Configuration is optional

The project default is already `.stacked`, so normal specs do not need this:

```
spec_config reference_view: .stacked,
            comparison_view: .stacked,
            dont_care_style: .dim
```

Its explicit expansion is:

```
spec_config(
    reference_view: .stacked,
    comparison_view: .stacked,
    dont_care_style: .dim,
)
```

A fixed layout requiring non-default word naming can register it once:

```
reference_layout NvmeWriteCommand,
    word_bits: 32,
    word_label: "CDW",
    first_word: 10
```

Equivalent internal representation:

```
register_reference_layout(
    NvmeWriteCommand,
    stacked_words(
        word_bits: 32,
        word_label: "CDW",
        first_word: 10,
    ),
)
```

### Override only where another view is better

```
reference NvmeWriteCommand, view: .field_table
reference NvmeWriteCommand, view: .bytes
reference HttpRequest, view: .grammar
reference AesGcmVector, view: .vector
```

Configuration precedence should be:

```
assertion override
    > reference invocation
    > registered type layout
    > describe/file configuration
    > project configuration
    > library default: stacked
```

### Scope behavior

| Placement | Meaning |
|---|---|
| File/global scope | Emit once in the document-level Reference section |
| Inside describe | Emit beside that feature; link if already emitted globally |
| Inside it with a type | Emit the schema locally |
| Inside it with a value | Emit a concrete observed-value layout |
| Repeated same type | Deduplicate by resolved type identity, not displayed name |

Quoted type names are forbidden:

```
# Bad: loses compile-time resolution
reference "NvmeWriteCommand"
```

Use a resolved type:

```
reference NvmeWriteCommand
```

---

## 2. Default generated struct layout

For the registered NvmeWriteCommand, this is the primary generated manual view.

```
31                                                        0
CDW10   ┌───────────────────────────────────────────────────────────────────────────┐
        │                           Starting LBA [31:0]                              │
        └───────────────────────────────────────────────────────────────────────────┘

CDW11   ┌───────────────────────────────────────────────────────────────────────────┐
        │                           Starting LBA [63:32]                             │
        └───────────────────────────────────────────────────────────────────────────┘

        31 30 29       26 25 24 23       20 19       16 15                        0
CDW12   ┌──┬──┬──────────┬──┬──┬──────────┬───────────┬─────────────────────────────┐
        │LR│FUA│ PRINFO  │RS│STC│ DTYPE   │ Reserved  │             NLB             │
        └──┴──┴──────────┴──┴──┴──────────┴───────────┴─────────────────────────────┘

        31                         16 15                         8 7                 0
CDW13   ┌────────────────────────────┬────────────────────────────┬──────────────────┐
        │           DSPEC            │          Reserved          │       DSM        │
        └────────────────────────────┴────────────────────────────┴──────────────────┘

CDW14   ┌───────────────────────────────────────────────────────────────────────────┐
        │                        Reference / Storage Tag                            │
        └───────────────────────────────────────────────────────────────────────────┘

        31                         16 15                                            0
CDW15   ┌────────────────────────────┬──────────────────────────────────────────────┐
        │    Application Tag Mask    │               Application Tag                │
        └────────────────────────────┴──────────────────────────────────────────────┘
```

This is one coherent raw-layout figure with multiple word rows. It is not:

- one separate table per dword;
- one 512-bit horizontal table;
- a generic `offset | field | type` reflection dump.

The field table is secondary documentation underneath the primary figure.

### Generated field specification

| Word | Bits | Field | Description | Compare policy | Invalid or reserved pattern |
|---|---|---|---|---|---|
| CDW10–11 | 63:0 | slba | Starting Logical Block Address | exact | Command-specific range validation |
| CDW12 | 31 | lr | Limited Retry | exact | — |
| CDW12 | 30 | fua | Force Unit Access | exact | — |
| CDW12 | 29:26 | prinfo | Protection Information | enum | Unassigned combinations invalid |
| CDW12 | 25 | reserved_25 | Reserved field | reserved_zero | Any non-zero bit |
| CDW12 | 24 | stc | Storage Tag Check | exact or context-conditioned | Context-specific |
| CDW12 | 23:20 | dtype | Directive Type | enum | Unsupported type |
| CDW12 | 19:16 | reserved_19_16 | Reserved field | reserved_zero | Any non-zero bit |
| CDW12 | 15:0 | nlb | Number of Logical Blocks | exact, decoded | Invalid command-specific range |
| CDW13 | 31:16 | dspec | Directive Specific | conditional | Invalid for selected directive |
| CDW13 | 15:8 | reserved | Reserved field | reserved_zero | Any non-zero bit |
| CDW13 | 7:0 | dsm | Dataset Management attributes | masked/bitfield | Reserved bit combinations |
| CDW14 | 31:0 | reference_tag | Reference or Storage Tag | conditional | Ignored only in specified contexts |
| CDW15 | 31:16 | application_tag_mask | Application Tag Mask | conditional | Context-dependent |
| CDW15 | 15:0 | application_tag | Application Tag | conditional | Context-dependent |

The labels and comments come from the actual type declaration and registered specification metadata. The renderer must not substitute an older field map merely because a prior NVMe version or example called the region "Reserved."

---

## 3. Expected/actual view uses the same layout

Matching full-width words remain compact. A mismatching bitfield word expands automatically.

```
CDW10   expected  0x0012_3400
        actual    0x0012_3400                                      ✓

CDW11   expected  0x0000_0000
        actual    0x0000_0000                                      ✓

CDW12   expected  0x5520_0007
        actual    0x5420_0007                                      FAIL

        expected
        ┌──┬───┬──────────┬──┬───┬──────────┬──────────┬───────────────────────────┐
        │0 │ 1 │   0101   │0 │ 1 │   0010   │   0000   │     0000000000000111      │
        └──┴───┴──────────┴──┴───┴──────────┴──────────┴───────────────────────────┘
          LR FUA  PRINFO   RS STC    DTYPE      Reserved              NLB

        actual
        ┌──┬───┬──────────┬──┬───┬──────────┬──────────┬───────────────────────────┐
        │0 │ 1 │   0101   │0 │ 0 │   0010   │   0000   │     0000000000000111      │
        └──┴───┴──────────┴──┴───┴──────────┴──────────┴───────────────────────────┘
                               ↑
                            STC FAIL
                       expected 1, actual 0
```

A context in which protection information is disabled can mark CDW14/CDW15 as don't-care:

```
CDW13   expected  0x0000_0000
        actual    0x0000_0000                                      ✓

CDW14   expected  ░0xDEAD_BEEF░
        actual    ░0x0000_0000░                                    ~ don't care
                                                                     PI disabled

CDW15   expected  ░0xFFFF_1234░
        actual    ░0x0000_0000░                                    ~ don't care
                                                                     PI disabled
```

The raw values are still retained in machine evidence; only their visual style and comparison mask change.

### Actual visual behavior

HTML/SVG manuals should render:

- don't-care fields with gray fill and muted text;
- masked-out sub-bits with gray hatching;
- the currently inspected field with a strong outline;
- a failing field with a red outline/background and a textual FAIL;
- a passing checked field normally;
- reserved-but-checked fields with a distinct "reserved" hatch, not don't-care gray.

Terminal output should use ANSI faint plus symbols. Markdown/plain-text fallback uses:

```
░value░   excluded from comparison
~         ignored/don't-care
^         active mismatch
✓         checked and equal
FAIL      checked and unequal
R0        reserved, must be zero
```

The result must never depend on color alone.

---

## 4. Comparison policies

The renderer is downstream of comparison semantics. It does not decide what is important by appearance.

The canonical rule is:

```
delta = (actual XOR expected) AND compare_mask
pass  = delta == 0
```

Each field contributes to compare_mask according to its policy and current context.

| Policy | Compared? | Rendering | Meaning |
|---|---|---|---|
| exact | Yes | Normal | Expected and actual bits must match |
| masked(mask) | Selected bits | Unselected bits gray | Only meaningful sub-bits are compared |
| dont_care | No | Gray/dim | Value is captured but cannot fail this assertion |
| ignore_when(condition) | Conditional | Gray when condition is true | Protocol/context-defined ignored field |
| reserved_zero | Yes | Reserved hatch | Must be zero |
| reserved_one | Yes | Reserved hatch | Must be one |
| one_of(values) | Yes | Normal | Actual value must be in the valid set |
| range(min,max) | Yes | Normal | Actual value must be in range |
| invalid(values) | Yes | Failure highlight | Prohibited encodings |
| noncanonical(values) | Decoder policy dependent | Warning/failure | May decode but encoder must not emit |
| derived(checker) | Yes | Derived marker | Checksum, length, parity, authentication tag |
| secret | Yes | Redacted text | Exact compare; value hidden from manual |
| documentation_only | No generated test | Labeled explicitly | Prose that cannot be automatically enforced |

A field shown as normative in the manual must be executable unless it is visibly marked documentation_only.

### Reserved and ignored must stay separate

This distinction prevents a dangerous false pass:

```
reserved_zero:
    expected 0
    actual   1
    result   FAIL

dont_care:
    expected any
    actual   any
    result   ignored
```

The current official NVMe material contains context-dependent fields that are ignored by the controller. Those are legitimate don't-care cases only when the SSpec scenario supplies the matching context.

---

## 5. Struct comments, field comments, and bad-pattern metadata

The type declaration remains the primary source of documentation.

Conceptually:

```
# Command-specific portion of an NVMe Write command.
struct NvmeWriteCommand:
    # Starting LBA, lower 32 bits.
    @bits(31, 0)
    slba_low: u32

    # Starting LBA, upper 32 bits.
    @bits(31, 0)
    slba_high: u32

    # Storage Tag Check.
    @bits(24)
    stc: bool

    # Reserved. Must be zero.
    @bits(25)
    @reserved_zero
    reserved_25: u1
```

The annotations are macro/attribute metadata using the existing language mechanism, not new core grammar.

For an external, generated, or immutable type, registration can add missing documentation:

```
reference_comment NvmeWriteCommand.cdw12.stc,
    "Controls checking of the storage tag."

reference_rule NvmeWriteCommand.cdw12.reserved_25,
    must_be: 0,
    violation: .invalid
```

Field paths must resolve to real type members. They must not be string paths such as `"cdw12.stc"`.

### Generated bad-pattern table

| Field | Value or pattern | Classification | Decoder behavior | Encoder behavior |
|---|---|---|---|---|
| reserved_25 | 1b | invalid | reject/report | never emit |
| dtype | unsupported value | invalid | command error | never emit |
| fuse | reserved combination | reserved | reject according to profile | never emit |
| application_tag | any value while PI is disabled | ignored | ignore | profile dependent |
| noncanonical length encoding | alternate valid representation | noncanonical | may accept | do not emit |

Enums should generate nested `Value | Definition | Status` tables automatically.

---

## 6. Canonical generated data model

Markdown and terminal text are projections. The authoritative result is typed SDN evidence.

```
binary_reference:
  schema_version: 1
  type_id: nvme.NvmeWriteCommand
  layout_id: nvme.write.v1_3
  view: stacked
  word_bits: 32
  word_label: CDW
  first_word: 10

  context:
    pi_enabled: false
    command_set: nvm
    spec_version: "1.3"

  words:
    - index: 10
      expected: 0x00123400
      actual: 0x00123400
      compare_mask: 0xffffffff
      delta: 0x00000000
      status: pass

    - index: 12
      expected: 0x55200007
      actual: 0x54200007
      compare_mask: 0xffffffff
      delta: 0x01000000
      status: fail

      fields:
        - path: cdw12.stc
          msb: 24
          lsb: 24
          expected: 1
          actual: 0
          policy: exact
          status: fail

    - index: 14
      expected: 0xdeadbeef
      actual: 0x00000000
      compare_mask: 0x00000000
      delta: 0x00000000
      policy: ignore_when
      reason: pi_disabled
      status: ignored
```

Every evidence object needs:

```
stable type ID
stable field path ID
schema/spec version
endianness
word size
significant bit length
expected bytes/bits
actual bytes/bits
comparison mask
context
first mismatch
all mismatches
semantic field mapping
rendering redaction policy
result
source/test location
```

This follows the existing modern-SSpec direction: typed evidence must cross the runner boundary, and one comparator/projection layer should serve binary, UI, protocol, and generated-manual output rather than using display strings as the data contract.

---

## 7. Default and optional reference views

### Default for structs

`.stacked`

Applies to: packed structs; bitfield structs; protocol headers; command descriptors; MMIO/register blocks; instructions; DMA descriptors; filesystem structures; executable-file structures; fixed binary file headers.

A full-width field occupies one row. Adjacent fields within one word share a row. A logical field spanning multiple words may occupy consecutive rows.

### Optional views

| View | Purpose |
|---|---|
| .stacked | Default multi-word/bitfield figure |
| .fields | Semantic field table |
| .bytes | Byte grid and ASCII |
| .words | Compact word-value grid |
| .bits | Flat bitstream |
| .grammar | ABNF/textual protocol grammar |
| .sequence | Request/response or state-machine exchange |
| .vector | Cryptographic known-answer vector |
| .algorithm | Inputs, outputs, prerequisites, steps |
| .flow | Processing/data-flow diagram |
| .blocks | Compression/container block sequence |
| .abi | Actual host/compiler ABI including padding |
| .custom | Registered domain renderer |

The normal `.stacked` view describes the wire/specification layout, not host ABI padding. ABI output must be explicitly requested with `.abi`.

---

## 8. Domain defaults

A struct still defaults to `.stacked`, but a domain can register another primary view for non-struct entities.

### NVMe, registers, instructions, file headers

```
reference NvmeWriteCommand
```

Primary: stacked words. Secondary: field table, nested value tables, invalid/reserved table, raw bytes.

### HTTP

```
reference HttpRequest, view: .grammar
```

Generated primary presentation:

```
request-line CRLF
field-line* CRLF
message-body?
```

Then: structured fields; constraints and bad patterns; concrete request/response example; optional byte representation.

HTTP/1.1 is specified as a start line, CRLF-terminated field lines, an empty line, and an optional body, so grammar and message sequence are more useful as the primary view than a synthetic fixed struct layout.

### Cryptography

For an algorithm:

```
reference aes_gcm_encrypt, view: .algorithm
```

Generated: Prerequisites, Input, Output, Steps, Security constraints.

For a known-answer vector:

```
reference AesGcmVector, view: .vector
```

Generated: Key / IV / AAD / plaintext / ciphertext / tag; lengths; expected versus actual; byte and bit differences; negative mutations.

That organization follows the way NIST describes GCM algorithms and publishes validation material.

### Compression

```
reference ZstdFrame
```

A frame struct can still use `.stacked`. A stream-level reference uses:

```
reference zstd_stream, view: .blocks
```

Generated: frame header, block 0, block 1, ..., checksum, significant bits, compressed size and ratio.

### Network protocols

Use both:

```
reference TcpHeader
reference tcp_exchange, view: .sequence
```

The packet/header uses stacked words. The connection uses a sequence table whose rows expand into the same binary evidence.

---

## 9. One unified SSpec binary architecture

Do not create separate frameworks for protocol, files, crypto, compression, structures, and bitstreams.

```
Type reflection + field comments + registered layouts
                         │
                         ▼
                SpecReferenceSchema
                         │
                         ▼
                  LayoutProjection
                         │
             ┌───────────┴───────────┐
             ▼                       ▼
       Expected evidence        Actual evidence
             └───────────┬───────────┘
                         ▼
              Mask-aware comparator
                         │
                         ▼
                    BinaryDiff
                         │
        ┌────────────────┼─────────────────┐
        ▼                ▼                 ▼
    Terminal        Markdown/HTML       SDN/JSON
    stacked          stacked/manual     machine result
```

Thin adapters feed this core:

```
BitStreamAdapter
StructAdapter
PacketAdapter
SequenceAdapter
FileAdapter
CryptoVectorAdapter
CompressionAdapter
RegisterAdapter
InstructionAdapter
```

The previous modern-SSpec plan already proposes a shared projection layer, structured byte/bit evidence, ignored-region visualization, and one canonical evidence/comparator pipeline. This work should complete that architecture instead of adding a parallel binary testing package.

---

## 10. SSpec comparison requirements by domain

### Bitstream

```
expect(actual).to_binary(
    expected,
    significant_bits: 117,
)
```

Requirements: bit length separate from storage byte length; comparison begins at an explicit bit order; trailing padding policy explicit; first differing bit and enclosing semantic field reported; masked ranges shown gray.

### Data structures

```
expect(actual).to_binary(
    expected,
    schema: NvmeWriteCommand,
)
```

Check both semantic field values and physical encoded bytes/bits. This catches a correct value stored at the wrong offset or with wrong endianness.

### File I/O

```
written = encode(index)
file.write(path, written)
read_back = file.read_bytes(path)

expect(read_back).to_binary(reference, schema: IndexFile)
```

Generated manual includes: file size, endianness, header/section layout, semantic fields, raw mismatch, checksum.

### Network protocols

```
step("Client sends request")
send(client, request)

step("Server returns response")
response = receive(client)

expect(response).to_binary(expected_response)
```

Generated sequence:

| # | Direction | Message | Size | Result |
|---|---|---|---|---|
| 1 | Client → Server | Request | 64 | pass |
| 2 | Server → Client | Response | 32 | fail |

Each row expands into the registered packet/message layout.

### Cryptography

Every cipher or authenticated-encryption migration needs: known-answer vectors; empty and boundary inputs; ciphertext bit corruption; AAD corruption; tag corruption; nonce/IV policy; wrong-key rejection; cross-implementation interoperability; secret redaction.

The manual redacts runtime secrets while machine evidence retains exact values in a protected artifact.

### Compression

Every codec needs:

```
Simple encode → Simple decode
C/reference encode → Simple decode
Simple encode → C/reference decode
corrupted stream rejection
truncated stream rejection
resource-limit/bomb handling
ratio, throughput, and memory regression
exact output only when the encoder contract is deterministic/canonical
```

For noncanonical encoders, interoperability and decoded data are authoritative; exact compressed-byte equality is not.

---

## 11. Consolidate existing repository work instead of duplicating it

The current repository already contains overlapping pieces:

- direct rt_* runtime-boundary cleanup;
- C-runtime exclusion analysis;
- custom primitive, transparent SFFI ABI, and bitfield metadata;
- primitive-public-API suppression cleanup;
- cross-language performance planning;
- SSpec typed evidence and generated-manual verification;
- verification rules requiring typed non-UI evidence and fresh workflow documentation.

Create one parent initiative:

```
binary_runtime_pure_simple_hardening
```

Its canonical registries should be:

```
binary_reference_layouts.sdn
runtime_boundary_inventory.sdn
c_migration_inventory.sdn
cross_language_perf_results.sdn
binary_test_coverage.sdn
```

Existing per-feature state files become source evidence, not parallel authorities.

### Merge duplicated utilities into four owners

```
std.binary.inspect
std.spec.binary
std.spec.table
spipe_docgen.reference
```

Audit and retire duplicate: hex dump functions, byte diff functions, bit diff functions, packet dumpers, binary schema builders, field table builders, protocol trace tables, crypto vector renderers, compression bitstream printers, manual Markdown table emitters.

Every old helper either:

1. delegates to the canonical implementation;
2. is migrated and deleted;
3. is retained with a documented incompatible requirement.

---

## 12. Direct rt_* hardening

### Required architecture

```
Product Simple code
        │
        ▼
Public semantic Simple API
        │
        ├── Pure Simple implementation
        │
        └── sanctioned zero-cost primitive alias
                    │
                    ▼
          private runtime/provider symbol
```

The public layer must not expose an `rt_` name.

Example:

```
# Provider module only
use runtime.primitive.{rt_memcpy as _memory_copy_primitive}

# Public semantic API
pub fn copy(dst: MutBytes, src: Bytes, count: Size):
    _memory_copy_primitive(dst, src, count)
```

Ordinary product code uses `std.memory.copy(dst, src, count)`, not `rt_memcpy(...)`.

### When an alias is permitted

Use a primitive alias only when all are true:

- the operation is a genuine runtime, compiler, syscall, hardware, or ABI primitive;
- Pure Simple cannot replace the boundary itself;
- the alias adds no wrapper frame or representation conversion;
- interpreter, JIT, AOT, native, bootstrap, and dynload lanes resolve the same target;
- the alias cannot collide with a local/imported symbol;
- ABI and debug/source behavior are verified;
- the provider is in an explicit allowlisted directory.

The current history demonstrates that selective-import aliases have previously diverged between entry modules, imported modules, JIT, and AOT. Therefore "the alias compiled" is insufficient: the check must run the produced program and prove that the intended symbol was reached in every lane.

### Why the old alias was deleted

The available evidence does not establish one trustworthy reason that the particular runtime aliases were removed. Do not guess that they were unnecessary.

The alias archaeology task must produce: alias name; introduction commit; removal commit; removed tests; parser/import behavior; interpreter behavior; JIT behavior; AOT/native behavior; symbol/relocation behavior; generated machine code; performance effect; final classification.

Required procedure:

```
git log -S<alias> --all
git blame around provider/import declarations
inspect removed regression tests
rebuild a fresh compiler
run interpreter/JIT/AOT/native resolution probes
compare MIR/LLVM/assembly
verify no extra call or conversion
```

The resulting `alias_removal_receipt.sdn` becomes a required artifact before reviving that alias family.

### Warning-to-error migration

**Phase A — immediately.** Critical/mission-critical builds: direct product rt_* is an error. Normal builds: existing occurrences warn. New occurrences beyond the measured baseline fail CI.

```
warning[W-RT-DIRECT]:
direct runtime symbol `rt_file_read_text` is forbidden in product Simple code

use:
    std.io.file.read_text(path)

provider-only alternative:
    import the sanctioned private alias from runtime.primitive

This warning is an error in critical mode.
Tracked migration: RT-DIRECT-0042
```

**Phase B — ratchet.** Every migrated occurrence reduces the baseline. The baseline may never increase.

**Phase C — zero product callers.** Once the product count reaches zero, promote the warning to a normal compiler/linter error everywhere.

**Phase D — delete compatibility handling.** Remove obsolete suppressions, compatibility externs, and stale aliases after all supported engines and bootstrap stages pass.

### Measured critical gate

Add a fail-closed checker such as `scripts/check/check-no-direct-rt.shs`. It must output structured counts:

```
rt_boundary:
  scanner_ran: true
  scanned_files: <measured>
  direct_total: <measured>
  allowed_provider: <measured>
  generated_boundary: <measured>
  test_oracle: <measured>
  forbidden_product: <measured>
  unclassified: <measured>
  aliases_registered: <measured>
  suppressions: <measured>
```

Required arithmetic:

```
direct_total
  = allowed_provider
  + generated_boundary
  + test_oracle
  + forbidden_product
  + unclassified
```

Final target:

```
scanned_files        > 0
forbidden_product    = 0
unclassified         = 0
suppressions         = 0
```

The checker must fail when: no files were scanned; its metrics are absent; the allowlist references a missing file or symbol; a count equation does not balance; a new provider directory appears without registration; a suppression lacks owner, reason, and expiry; the scanner itself is bypassed.

Self-test fixtures must include:

```
ordinary direct call        → FAIL
sanctioned provider call    → PASS
indirect alias collision    → FAIL
empty tree                  → ERROR, not PASS
stale allowlist             → FAIL
removed scanner loop        → ERROR
new unclassified symbol     → FAIL
```

Register this checker in every critical-check roster and in the verification skill. The existing verification guidance already rejects certain new raw runtime accesses and requires runtime-facade guards, so the new gate generalizes an existing policy rather than creating a competing one.

---

## 13. "Simple can do what C can do"

The final target is:

> All project-owned production behavior that can be expressed in C must be expressible and implemented in Simple. Any inability becomes a Simple language/compiler/runtime capability bug, not a permanent reason to keep product logic in C.

This does not mean rewriting third-party libraries merely because their upstream implementation is C.

### C classification

Every non-vendored C source must have exactly one class:

| Class | Final treatment |
|---|---|
| Project-owned product algorithm | Migrate to Pure Simple |
| Runtime/compiler primitive | Pure Simple or sanctioned private primitive provider |
| Platform ABI shim | Minimize; generate where possible; explicitly retained |
| Bootstrap stage | Migrate by staged self-hosting plan |
| Third-party implementation | Retain externally; Simple facade/binding |
| Conformance/reference oracle | Test-only; never production-linked |
| Generated source | Regenerate from the Simple authority |
| Dead/unbuilt duplicate | Delete |
| Unclassified | Critical failure |

The existing C-runtime audit has already removed numerous zero-caller files and identifies active areas including memory, time, native value/I/O, process/threading, media wrappers, SIMD, database/SQLite, bootstrap, MCP, optional OpenSSL, and WASM boundaries. That inventory should be imported into the new registry rather than recreated manually.

### Canonical migration record

```
c_migration:
  id: C-MIG-0042
  path: src/runtime/runtime_memory.c
  symbols:
    - rt_alloc
    - rt_free
    - rt_memcpy

  classification: runtime_primitive
  production_build_lanes:
    - native
    - bootstrap

  simple_callers: [...]
  rust_callers: [...]
  generated_callers: [...]

  simple_capability_blocker: SIMPLE-CAP-0017
  correctness_spec: test/.../memory_provider_spec.spl
  differential_spec: test/.../memory_provider_crosslang_spec.spl
  performance_spec: test/05_perf/.../memory_provider_perf_spec.spl

  replacement: std.memory.provider
  status: planned
```

The bug taxonomy should be:

```
RT-DIRECT
ALIAS-PARITY
C-MIGRATION
SIMPLE-CAPABILITY
ABI-MISMATCH
PERF-REGRESSION
BINARY-SSPEC
PROTOCOL-COMPAT
CRYPTO-COMPAT
COMPRESSION-COMPAT
DUPLICATION
DOCGEN
```

One SDN registry generates the human bug list and dashboard. Agents must not maintain independent Markdown backlogs that drift.

---

## 14. Shared C/Rust/Simple/Pure-Simple HAL process

The initial C HAL is an oracle and compatibility provider, not the permanent architectural center.

### Canonical sequence

**Step 1 — freeze one HAL contract.** Define the contract in Simple/SDN and generate all language-facing bindings:

```
HalContract
   ├── generated C header
   ├── generated Rust declarations
   ├── Simple SFFI declarations
   └── Pure Simple interface
```

Example surface:

```
interface BlockDeviceHal:
    fn read(offset: u64, out: MutBytes) -> HalResult
    fn write(offset: u64, data: Bytes) -> HalResult
    fn flush() -> HalResult
    fn capability() -> BlockDeviceCapability
```

**Step 2 — implement the first provider in .c** (`hal_c`). All current lanes call the same ABI: Rust seed, Simple interpreter, Simple JIT, Simple AOT, Pure Simple library. This establishes one known baseline before replacing it.

**Step 3 — capture deterministic I/O evidence.** Every call records: operation, arguments, input bytes, output bytes, return code, device-visible command, ordering/barriers, timing.

**Step 4 — add providers:** `hal_c`, `hal_rust`, `hal_simple`, `hal_pure_simple`. They implement exactly the same generated contract.

**Step 5 — differential execution.** For read-only or deterministic operations: run all providers, compare outputs. For destructive hardware operations, do not execute the write four times. Use:

```
real execution once
    → command trace
    → deterministic fake/replay device
    → execute other providers against replay
    → compare command streams and results
```

Split the interface into: query operations, command construction, command submission, result decoding. That makes most of the algorithm differential-testable without duplicate device side effects.

**Step 6 — shadow mode.** During migration: primary provider executes; secondary provider computes expected command/output; SSpec compares them; only primary side effects are committed.

**Step 7 — production flip.**

```
Pure Simple becomes primary
C remains test oracle for a bounded stabilization period
C production linkage is removed
C oracle moves under test/reference
C source is deleted when independent coverage is sufficient
```

### Cross-provider matrix

| Producer | Consumer/checker |
|---|---|
| C | C/reference |
| C | Rust |
| C | Simple |
| C | Pure Simple |
| Rust | C |
| Simple | C |
| Pure Simple | C |
| Simple | Rust |
| Pure Simple | Simple |

For serialized formats and protocols, both directions are mandatory.

For hardware operations, compare: normalized command stream, MMIO/register writes, DMA descriptors, barrier ordering, returned data, error semantics.

---

## 15. Independent algorithm oracles

Where the same semantics exist in an independent mature project, add it as a third oracle. Examples:

- Chromium URL canonicalization tests for Simple URL/web handling;
- RFC examples for HTTP;
- official NVMe field and command constraints;
- NIST validation vectors for cryptography;
- reference codec implementations and official corpora for compression.

Chromium's URL canonicalization test corpus is useful for URL behavior because it provides an independent implementation and concrete expected outputs; it should be pinned to a commit and used only where Simple intends identical semantics.

Do not use "Chrome agrees" as a universal oracle for unrelated storage, crypto, or HAL behavior.

---

## 16. Simple must equal or beat C

The migration gate is:

> A project-owned hot-path C implementation is not removed until the Pure Simple replacement is correct and either faster or statistically equivalent without an intentional performance concession.

The 2% band below is a measurement/noise band, not permission to design a 2% slower implementation.

### Benchmark contract

Every result records: source commit; compiler/runtime commit; binary hash; execution engine; optimization level; LTO/vectorization settings; host CPU and OS; CPU affinity/governor; input corpus hash; warm-up count; iteration count; interleaving method; median; p95; dispersion/CV; allocations; peak RSS; code size; output checksum.

Use release/native builds for C-vs-Simple product comparison. Interpreter performance is a separate lane.

Google Benchmark's documented facilities for warm-up, repetitions, aggregate statistics, and randomized interleaving provide a sound model for reducing drift and reporting median/dispersion rather than trusting one timing.

### Performance verdict

Let `R = Simple median / C median`.

| Verdict | Condition |
|---|---|
| Faster | Confidence interval upper bound below 1.00 |
| Equivalent | Median no worse than C and upper noise bound within 1.02 |
| Investigate | Result within noise but Simple median above C, or high variance |
| Fail | Statistically material regression above 2% |
| Critical fail | Median regression above 5%, unexplained fallback, or different work performed |

A result is invalid when: output differs; one implementation performs less validation; one uses cached/precomputed data not available to the other; the Simple lane silently falls back from JIT/native to interpreter; input or allocation behavior differs materially; benchmark execution count is zero.

### Performance-bug workflow

When Simple loses:

```
PERF-BUG
    ↓
profile both implementations
    ↓
compare allocations and copies
    ↓
compare Simple MIR
    ↓
compare LLVM/native IR
    ↓
compare assembly
    ↓
classify root cause
```

Root-cause categories: extra wrapper/alias call; FFI transition; allocation/copy; bounds check; failure to inline; failure to vectorize; poor alias information; branch/layout issue; integer width conversion; endianness conversion; JIT fallback; runtime dispatch; startup/load cost; code-size/I-cache regression.

Prefer fixing the compiler/runtime mechanism so every Pure Simple implementation benefits. The repository's prior performance work already found cases where an assumed call-site "optimization" was only a correctness change, while runtime-level changes produced broader improvements. That lesson should be codified in the migration process.

---

## 17. Parallel-agent plan

### Wave 0 — freeze shared contracts

Only one architecture owner edits these interfaces:

```
SpecReferenceSchema
StackedWordLayout
BinaryEvidence
BinaryComparison
BinaryDiff
HAL contract schema
runtime-boundary classification
C-migration classification
performance result schema
```

Outputs:

```
doc/04_architecture/sspec_binary_reference.md
doc/05_design/sspec_stacked_layout.md
binary_reference_schema.sdn
runtime_boundary_schema.sdn
c_migration_schema.sdn
cross_language_perf_schema.sdn
```

A second high-capability reviewer checks: no grammar addition; stacked default; reserved/don't-care separation; context-sensitive masks; stable type/field IDs; engine-neutral alias contract; no duplicate evidence pipeline.

No migration agent starts until these contracts are frozen.

### Wave 1 — read-only audits in parallel

**Agent A — rt_* and alias archaeology.** Owns: direct rt_ inventory, provider classification, critical-check rosters, alias introduction/removal history, alias engine-parity matrix, baseline counts. Must not edit product callers yet.

**Agent B — C inventory.** Owns: all non-vendored .c/.h units, actual build inputs, symbols, callers, classification, replacement/blocker, bug import. Imports the existing C-runtime audit.

**Agent C — SSpec binary duplication audit.** Finds: hex/byte/bit diff helpers, bitfield renderers, packet dumpers, protocol visualizers, file comparison utilities, manual table emitters, crypto/compression vector utilities. Produces a merge/delete map.

**Agent D — performance infrastructure audit.** Owns: existing cross-language harness, benchmark result formats, fresh-binary provenance, JIT fallback detection, candidate C/Simple comparisons, host reproducibility.

**Agent E — protocol/security/compression corpus.** Owns: HTTP and packet fixtures, NVMe structures and contexts, crypto KATs and negative vectors, compression interoperability corpora, large/boundary/malformed cases.

**Agent F — SPipe skill and LLM wiki audit.** Finds every process document that must change: SPipe skill, verify skill, refactor skill, system-test skill, LLM wiki/rules, docgen guide, critical-check guide, C migration guide, performance guide.

All six agents write separate audit reports but update one read-only aggregate SDN through the merge owner.

### Wave 2 — core SSpec implementation

**Agent 1 — type/layout extraction.** Owns: reflection → SpecReferenceSchema, struct/bitfield comments, stable field IDs, registered external layouts, nested type references.

**Agent 2 — comparator.** Owns: exact, masked, dont_care, reserved_zero/one, conditional policies, significant bits, endianness, first/all mismatch calculation.

**Agent 3 — stacked renderer.** Owns: multi-word stacking, proportional field widths, full-width fields, multiword fields, long labels, active/fail highlighting, gray don't-care regions, terminal fallback.

**Agent 4 — manual renderer.** Owns: Markdown, HTML/SVG, field tables, value tables, bad-pattern tables, anchors, global/local reference deduplication.

**Agent 5 — machine evidence.** Owns: SDN/JSON serialization, schema versioning, artifact persistence, source/type/field mapping, redaction.

**Agent 6 — domain adapters.** Owns: bitstream, file, packet, sequence, crypto vector, compression blocks, register/instruction.

Core agents must use golden fixtures; none may invent a second comparator or table model.

### Wave 3 — rt_* gate and alias infrastructure

**Central alias owner** implements: sanctioned alias registry, zero-cost proof, cross-engine resolution probes, duplicate/collision diagnostics, provider-only visibility, fix-it metadata.

**Guard owner** implements: check-no-direct-rt, selftests, baseline ratchet, critical roster registration, structured metrics, compiler/linter diagnostic.

**Migration agents by non-overlapping subsystem:** compiler and codegen; stdlib and application; OS and HAL; graphics/GPU/media; network/database/security; tests and tooling.

Each agent reports: baseline count, migrated count, remaining count, provider exceptions, spec results, fresh binary hash.

No agent may create a local rt_* wrapper merely to make the scanner green.

### Wave 4 — C-to-Simple migrations

Split by ownership: memory/time/native core; process/thread/file/network; database/SQLite; audio/font/image/SDL; SIMD/text/crypto/compression; bootstrap/MCP/WASM/HTTPS; OS and hardware HAL.

For each migration:

1. Freeze C behavior.
2. Add SSpec binary/I/O evidence.
3. Add independent vector/corpus where available.
4. Implement Pure Simple.
5. Run C/Rust/Simple/Pure-Simple differential matrix.
6. Run performance benchmark.
7. File and fix Simple capability or performance bugs.
8. Switch production provider.
9. Retain C as test oracle temporarily.
10. Delete or explicitly classify retained C.

### Wave 5 — performance closure

Optimization agents receive only red or inconclusive benchmark IDs. They do not own functional migration code.

Assignments divided by root cause: allocation/copy; bounds checks and alias analysis; inlining/call lowering; SIMD/vectorization; runtime dispatch; JIT/AOT divergence; startup/load/code size.

Every fix reruns the complete affected benchmark corpus, not just the initially failing case.

### Wave 6 — documentation and duplication closure

Parallel checks: generated manuals; SSpec maintenance scan; skill/wiki freshness; duplicate helper deletion; critical metric dashboards; bug registry consistency; all referenced commands still exist.

The existing verification skill already requires generated manuals, typed evidence, performance benchmarks, and workflow-document freshness. The new binary and runtime gates should become explicit requirements there.

### Parallel-work conflict rules

1. One owner per shared interface.
2. One owner per canonical registry.
3. Agents use separate worktrees/branches.
4. No agent edits another agent's audit result.
5. Merge owner resolves registry updates.
6. Every interface change increments a schema version.
7. Every generated artifact is deterministic and idempotent.
8. Every agent provides baseline/current counts.
9. Every test receipt records the fresh binary hash.
10. No completion claim based only on compilation.
11. No green result with zero examples or zero files scanned.
12. No weakening of an oracle to make a migration pass.
13. All failed/inconclusive results remain visible.
14. Highest-capability final review verifies the merged architecture and generated manuals.

---

## 18. Critical release gates

| Gate | Final requirement |
|---|---|
| Files scanned by rt_* checker | > 0 |
| Forbidden direct product rt_* | 0 |
| Unclassified rt_* occurrences | 0 |
| rt_* suppressions | 0 |
| Sanctioned aliases without cross-engine proof | 0 |
| Alias resolution/collision tests | pass in interpreter, JIT, AOT, native |
| Unclassified project-owned C sources | 0 |
| Replaceable project-owned production C | 0 |
| C migration items lacking I/O differential test | 0 |
| Hot migrations slower than C beyond noise | 0 |
| Simple capability blockers hidden by C workaround | 0 |
| Binary comparator self-tests | pass |
| Reserved-vs-don't-care mutation tests | pass |
| Significant-bit/non-byte-aligned tests | pass |
| Stacked renderer golden tests | pass |
| Markdown/HTML/TUI semantic parity | pass |
| HTTP/protocol interoperability | pass |
| Crypto KAT and corruption tests | pass |
| Compression cross-decoder tests | pass |
| Generated manuals with unresolved stubs | 0 |
| Duplicate binary diff/render helpers | target 0 |
| Stale SPipe/verify/refactor/wiki guidance | 0 |
| Vacuous critical checks | 0 |

Every critical checker emits counts, not merely PASS.

---

## 19. Implementation order

The safe order is:

1. Freeze reference/evidence schemas.
2. Land stacked-layout golden examples.
3. Implement compare masks and reserved/don't-care semantics.
4. Implement stacked terminal and Markdown/HTML renderers.
5. Connect `reference Type` globally/describe/it.
6. Add protocol/file/crypto/compression adapters.
7. Audit and merge duplicate helpers.
8. Land direct-rt scanner and measured baseline.
9. Prove or reject the zero-cost alias mechanism.
10. Enable critical-mode rt errors.
11. Import the existing C inventory into one registry.
12. Land the common HAL differential framework.
13. Migrate rt callers and C implementations by subsystem.
14. Fix Simple capability and performance bugs.
15. Flip providers to Pure Simple.
16. Promote direct-rt warnings to universal errors.
17. Remove production C and obsolete compatibility paths.
18. Update SPipe skills, verification rules, and LLM wiki.
19. Run the complete measured critical gate.

## Final target state

`reference SomeType` produces a beautiful vertically stacked multi-word layout by default.

`expect(actual).to_binary(expected)` reuses that exact layout, expands only meaningful failures, highlights the checked field, and grays only true don't-care regions.

Product code has:

```
zero direct rt_* use
zero unclassified C
Pure Simple semantic APIs
sanctioned zero-cost aliases only at private provider boundaries
cross-language I/O equivalence
Simple performance equal to or faster than C for migrated hot paths
one shared SSpec evidence/comparison/manual pipeline
```

That gives the binary hardening program one coherent architecture rather than separate rt_, C migration, HAL, protocol, crypto, compression, performance, and documentation projects.

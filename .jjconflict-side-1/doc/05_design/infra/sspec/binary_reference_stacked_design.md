# Design — SSpec Binary Reference (Stacked Layout) + Comparison Semantics

Status: design (frozen surface), 2026-08-18.
Source research: `doc/01_research/infra/sspec_binary/binary_sspec_rt_hardening_frozen_design_2026-08-18.md`
Builds on: `doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md` (this design COMPLETES that pipeline; it does not add a parallel one).

## Authoring surface (no grammar change)

```
use std.spec.*

reference NvmeWriteCommand              # macro → reference(NvmeWriteCommand)

describe "NVMe Write command":
    it "encodes the command-specific dwords":
        expect(actual).to_binary(expected)
```

- `reference Type` — resolved type only, never a quoted string. Dedup by type identity.
- Default view for every fixed-layout struct: `.stacked` (vertically stacked multi-word figure). Other views (`.fields .bytes .words .bits .grammar .sequence .vector .algorithm .flow .blocks .abi .custom`) are opt-in.
- Precedence: assertion override > reference invocation > registered type layout > describe/file config > project config > library default (stacked).
- `reference_layout Type, word_bits:, word_label:, first_word:` registers non-default word naming once.
- `reference_comment` / `reference_rule` attach docs/rules to external or generated types; field paths must resolve to real members.

## Comparison semantics (renderer is downstream, never decides)

```
delta = (actual XOR expected) AND compare_mask ; pass = delta == 0
```

Policies: `exact, masked(mask), dont_care, ignore_when(cond), reserved_zero, reserved_one, one_of, range, invalid, noncanonical, derived(checker), secret, documentation_only`.

Two hard rules:
1. Gray = genuinely excluded (`compare_mask = 0` under the current context).
2. Reserved ≠ gray: `reserved_zero/one` and prohibited encodings are actively checked. A reserved bit flipping is a FAIL, never an ignore.

## Rendering

- Reference manual: one coherent stacked figure (bit ruler + word rows, proportional field widths), then a secondary field table and bad-pattern table.
- Expected/actual: matching full-width words stay compact (`expected/actual/✓`); a mismatching bitfield word auto-expands to the bit-level stacked pair with the failing field highlighted (`STC FAIL, expected 1, actual 0`).
- Don't-care words render `░value░ ~ don't care (reason)`; raw values retained in machine evidence.
- Terminal: ANSI faint + symbols (`✓ FAIL ~ ^ R0 ░`); never color-only. HTML/SVG: gray fill for don't-care, hatch for reserved, red outline for fail.

## Canonical data model

Authoritative result is typed SDN (`binary_reference:` — schema_version, type_id, layout_id, view, word geometry, context, per-word expected/actual/compare_mask/delta/status, per-field mismatch records). Markdown/terminal/HTML are projections. Full example in the research doc §6.

## Architecture (one pipeline, thin adapters)

```
reflection + comments + registered layouts → SpecReferenceSchema → LayoutProjection
  → expected/actual evidence → mask-aware comparator → BinaryDiff
  → {terminal, markdown/html, SDN/JSON}
```

Adapters: BitStream, Struct, Packet, Sequence, File, CryptoVector, Compression, Register, Instruction. No second comparator or table model anywhere.

Canonical owners: `std.binary.inspect`, `std.spec.binary`, `std.spec.table`, `spipe_docgen.reference`. Duplicated hex/byte/bit-diff/dump/table helpers get merged into these or deleted.

## Domain requirements (summary; detail in research §10)

- Bitstream: `significant_bits:` separate from storage length; first differing bit + enclosing field reported.
- Structs: check semantic field values AND physical bytes (catches wrong offset/endianness).
- Files: size, endianness, layout, checksum in generated manual.
- Protocols: `.sequence` table whose rows expand into registered packet layouts.
- Crypto: KATs + corruption/negative vectors; secrets redacted in manuals, exact in protected evidence.
- Compression: cross-encoder/decoder matrix; exact bytes only for canonical encoders.

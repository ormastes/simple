# SMF header wire layout diverges between the Simple and Rust implementations

**Date:** 2026-08-10
**Status:** OPEN — ARCHITECTURAL, confirmed genuinely out of scope for a unilateral fix.
Re-verified fresh 2026-08-10: root cause, offset table, and parity-spec pass (7/7) all
reproduced independently from source; the round-trip gap flagged in the original filing
is now closed (see "Round trip executed and recorded" below) — the divergence is **live**,
not latent: `object_provider.spl` parses real on-disk `.smf` files with the packed-offset
reader and would misdecode any Rust-seed-written file with a non-empty section table.
A fix requires the dual-write migration below; changing either layout unilaterally would
invalidate every existing cached artifact, which is why no code fix is applied in this pass.
**Severity:** blocks the `.simple_meta` metadata work (targeted-build plan §13.1 P0 gate).
**Found by:** SMF format audit (agent A6), independently re-verified by the reviewing model,
and re-verified again 2026-08-10 (round-trip evidence added, no findings changed).

---

## Claim

The pure-Simple and Rust-seed SMF headers are **not wire-identical**. They disagree on
header size, on the trailer location, and on the byte offset of every field from
`section_table_offset` onward.

The originating plan (`doc/03_plan/compiler/build_system/targeted_build_interface_compat_minimal_bootstrap_2026-08-10.md` §2.5)
guessed "5 reserved bytes vs 40". That is true but **understates** the problem: the real
divergence is structural alignment padding, not just a reserved-byte count.

## Evidence

### Root cause — `#[repr(C)]` alignment padding

`src/compiler_rust/common/src/smf/header.rs:7` declares `#[repr(C)]`. Field layout:

```
magic[4] version_major version_minor platform arch   → 0..8
flags: u32                                            → 8   (aligned)
compression, compression_level, reserved_compression[2] → 12..16
section_count: u32                                    → 16
section_table_offset: u64                             → needs 8-alignment
                                                      → 4 PADDING BYTES at 20..24
                                                      → lands at 24
```

The Simple writer places `section_table_offset` at **20** — packed, no padding
(`src/compiler/70.backend/linker/smf_header.spl`, offsets are integer literals in
`smf_header_from_bytes`; reader mirrors them in `header_parser.spl`).

Every subsequent field is therefore shifted by 4 bytes.

### Measured divergence table

| Item | Simple (`70.backend/linker/smf_header.spl`) | Rust seed (`compiler_rust/common/src/smf/header.rs`) |
|---|---|---|
| Header size | **128** (packed, `SMF_HEADER_SIZE:27`) | **96** (`SIZE = size_of::<Self>()`) |
| Trailer locator | EOF − 128 | EOF − 96 |
| `section_table_offset` | 20 | **24** |
| `symbol_table_offset` / `symbol_count` / `exported_count` | 28 / 36 / 40 | **32 / 40 / 44** |
| `entry_point` / `stub_size` / `smf_data_offset` | 44 / 52 / 56 | **48 / 56 / 60** |
| `module_hash` / `source_hash` / `app_type` | 60 / 68 / 76 | **64 / 72 / 80** |
| `reserved` | 40 B @ 88..128 | **5 B** @ 88..93 |
| compile-options hash | `reserved[0..16]` = bytes 88..104 | **does not exist** |
| Serialization | explicit little-endian, field by field | **raw struct memcpy** (`std::ptr::read` cast) |

The Rust side is not serializing a wire format at all — it `unsafe`-casts the byte buffer
to the native struct. Its "format" is therefore whatever the host ABI produces, which is
also why the padding leaked into the file layout in the first place.

### Verification performed

- A compiled `offset_of` probe of the real Rust struct reported `SIZE 96`,
  `section_table_offset 24`, `entry_point 48`, `app_type 80`, `reserved 88`.
- Reviewer independently re-derived the same offsets from the struct declaration and
  confirmed `#[repr(C)]` at `header.rs:7`.
- Regression pin: `src/compiler/70.backend/linker/test/smf_layout_parity_spec.spl`
  — `SPEC FILE VERDICT ... declared>=7 executed=7 passed=7 failed=0 dropped=0`
  (re-run by the reviewer in the main tree, not relayed). Sabotage probe: flipping the
  compile-options offset assertion 0x88→0x87 produced `passed=6 failed=1`; reverted to 7/7.

### Round trip executed and recorded (2026-08-10, re-investigation)

Independently re-verified all of the above from source (`src/compiler_rust/common/src/smf/header.rs:9-35`
struct field list, `src/compiler/70.backend/linker/smf_header.spl` offsets, and a fresh run of
`smf_layout_parity_spec.spl` → `declared>=7 executed=7 passed=7 failed=0 dropped=0`, matching the
prior claim exactly).

The previously-open "NOT verified" item is now closed. Real `.smf` artifacts already on disk in
this tree (`build/dynsmf/net_io.smf`, `build/enum_exposure/p_eq_native.smf`, both written by the
only toolchain currently producing them, the Rust seed) were decoded byte-for-byte under both
candidate offset schemes:

```
section_count @16 = 3 (net_io.smf) / 7 (p_eq_native.smf)  — sane either way
section_table_offset read @20 (Simple packed offset):  412316860416   ← garbage
section_table_offset read @24 (Rust padded offset):     96            ← correct (= header size)
```

This confirms the files on disk use the Rust `#[repr(C)]` padded layout, and that reading them
at the Simple packed offset produces exactly the garbage the doc predicted. Header location was
also confirmed empirically to be **at offset 0** in every sampled file (`SMF\0...` magic bytes at
byte 0), not at the EOF trailer both header.rs and smf_header.spl also support — so the trailer-vs-
header-front question is moot for files actually being produced today; only the packed-vs-padded
field-offset divergence is live.

Crucially, this is **not latent**: `src/compiler/70.backend/linker/object_provider.spl:160,201`
calls `smf_header_from_bytes` (the packed-offset Simple parser) directly against real `.smf` files
read from disk — this is the live pure-Simple SMF loader path, not dead/test-only code. Any
pure-Simple toolchain component that loads a Rust-seed-written `.smf` today hits the misparse
described below in normal operation, not just in a hypothetical cross-toolchain scenario.

The failure mode when it IS exercised: a Simple reader parsing a Rust-written SMF decodes
garbage from byte 20 onward. Because each side looks for its trailer at a different offset
from EOF, the other side's magic check fails and it silently falls back to a v1.0
offset-0 parse — a **misparse, not a clean error**.

## Constraint on any fix

Do **not** change either layout unilaterally. Both sides have written artifacts that are
presumably cached on disk. The migration is plan §13.5's dual-write:

1. Publish `src/spec/artifact/smf_v1_2.sdn` as the single normative layout (landed).
2. Generate or validate BOTH headers against it; make the parity test fail-closed in CI.
3. Dual-write old + new representations during transition; prefer the new on read.
4. Stop writing the old representation only after every supported reader consumes the new.
5. Treat conflicting duplicate metadata as corruption, never as a cache hit.

And per the plan's own rule: **allocate no new fixed-header byte.** New metadata goes in
the `.simple_meta` TLV section precisely so the header never has to move again.

## Artifacts landed with this record

- `src/spec/artifact/smf_v1_2.sdn` — normative schema: v1.0/v1.1 packed layout, the v1.2
  `.simple_meta` TLV design, `InterfaceCompatibilityV1` (72 B payload), and a divergence
  audit block. No new header bytes allocated.
- `src/compiler/70.backend/linker/test/smf_layout_parity_spec.spl` — 7 tests pinning the
  Simple layout and the known Rust divergence, so an accidental "fix" to either side is
  caught rather than silently shipped.

---

## Independently re-derived 2026-08-17 — CONFIRMED LIVE, offsets exact

Recomputed from first principles by applying C `#[repr(C)]` natural-alignment
rules to `src/compiler_rust/common/src/smf/header.rs:9` and comparing against
the Simple decoder at `src/compiler/70.backend/linker/smf_header.spl:476-509`.
Arrived at the same numbers the existing spec records, without consulting it —
so the two derivations are independent.

The divergence begins at the first `u64` after a `u32`. `section_count: u32`
ends at 20; `section_table_offset: u64` must be 8-aligned, so Rust inserts 4
bytes of padding and places it at **24**. The Simple layout is PACKED and reads
it at **20**. Every subsequent field is displaced, and the totals differ:

| field | Rust `repr(C)` | Simple packed | delta |
|---|---|---|---|
| `section_table_offset` | 24 | 20 | +4 |
| `symbol_table_offset` | 32 | 28 | +4 |
| `symbol_count` | 40 | 36 | +4 |
| `exported_count` | 44 | 40 | +4 |
| `entry_point` | 48 | 44 | +4 |
| `stub_size` | 56 | 52 | +4 |
| `smf_data_offset` | 60 | 56 | +4 |
| `module_hash` | 64 | 60 | +4 |
| `source_hash` | 72 | 68 | +4 |
| `app_type` | 80 | 76 | +4 |
| `window_width` | 82 | 77 | +5 |
| `window_height` | 84 | 79 | +5 |
| `prefetch_hint` | 86 | 81 | +5 |
| `prefetch_file_count` | 87 | 82 | +5 |
| **struct size** | **96** | **128** | **+32** |

Fields 0..20 (magic, version, platform, arch, flags, compression,
compression_level, reserved_compression, section_count) agree exactly — which is
why a shallow "does it parse" check passes and the misdecode stays silent.

The trailer location differs too: Rust reads at EOF-96, Simple at EOF-128.

**Not fixed here, and deliberately so.** Converging the two requires editing
`src/compiler_rust/common/src/smf/header.rs` (either `#[repr(C, packed)]` plus a
128-byte definition, or moving Simple onto the padded 96-byte layout). That is
outside this session's exclusive scope (`src/compiler/70.backend/**`) and is a
wire-format decision affecting every SMF producer and consumer in both
languages. Recording the exact numbers so whoever takes it does not have to
re-derive them.

Already guarded: `src/compiler/70.backend/linker/test/smf_layout_parity_spec.spl`
pins the Simple side byte-for-byte and records `RUST_SEED_HEADER_SIZE = 96`,
`RUST_SECTION_TABLE_OFFSET = 24`, `RUST_ENTRY_POINT_OFFSET = 48`,
`RUST_APP_TYPE_OFFSET = 80` — all matching the table above.

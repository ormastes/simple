# Hash256 wire contract v1 — frozen

The 256-bit content-hash field type architecture §26 names in three artifact
groups and defines in none. This closes the last undefined scalar in the
MDSOC+ contract freeze.

Architecture:
`doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
§20.3 (`receipt_seed`), §21.3 (`input_root` / `output_root` /
`deterministic_hash`), §26 (contract freeze), §27 (lane ownership).

- Simple types + CPU reference codec: `src/lib/common/structural/digest/`
- Golden vectors: `test/fixtures/structural/hash256_golden_v1.{spl,sdn}`
- Gate: `test/01_unit/common/structural/hash256_contract_spec.spl`

## Why this was needed — three lanes, three answers

`Hash256` was not merely undefined. It was defined three incompatible ways by
three lanes that each reported success. All three are in tree at
`55115a82411`:

| Lane | Field | Encoding shipped | Accepts |
|---|---|---|---|
| PLACE | `PlacementPlan.receipt_seed` | **32 raw bytes**, fixed (`place_put_hash`, `PLACEMENT_HASH_LEN = 32`) | 64 lowercase hex characters only |
| RECEIPT | `StageReceipt.input_root` / `output_root` / `deterministic_hash` | **u32 length prefix + ASCII text**, variable (`receipt_put_text`, guarded by `receipt_text_ascii`) | **any ASCII**, including `""` |
| MUTATE | `MutationPlan.plan_hash` | *declined* — deviated to `Hash128`, recording that `Hash256` "exists in-tree only as a `text` wrapper class" | — |

A `PlacementPlan` and a `StageReceipt` carrying the same digest therefore
produce different bytes for it, and only one of the two can be re-derived from
the other's wire form. `staged_backend.spl` writes
`Hash256(value: "staged_empty")` — a value that is not a hash at all and that
the RECEIPT encoding accepts silently.

This contract freezes **one** encoding and adopts the PLACE form **verbatim**
rather than minting a fourth vocabulary. That is the same call the PLACE lane
itself made when it adopted the EXEC lane's `DeviceMask` bit vocabulary instead
of restating it: *"a second vocabulary for one wire field is exactly the
divergence the freeze exists to prevent."*

## Conventions

Inherited unchanged from the ID-TAG lane's frozen port
`src/lib/common/structural/wire.spl`: little-endian, fixed width, no padding,
no alignment; decoders total and returning an ok flag; malformed input **hard
rejected**, never silently defaulted.

## What this group does NOT redeclare

`class Hash256: value: text` already exists in
`src/lib/common/compute/placement_contracts/semantic.spl`. It is the host-side
carrier and is **not** redeclared here — two declarations of one wire type is
how two lanes come to disagree about a field while both report success. This
group adds the byte layout and the rules over that carrier's `text` value.

`Hash128` stays in `structural/identity` (ID-TAG lane) and is untouched.

## Layout — frozen

```text
Hash256   32   b0 b1 b2 ... b31

  byte i = characters 2i and 2i+1 of the 64-character lowercase hex host
           spelling, HIGH NIBBLE FIRST
```

**No envelope. No magic. No length prefix. No schema version of its own.**

`Hash256` is a **field type**, exactly like `Hash128`. It inherits the envelope
and the schema version of whatever record embeds it. A digest that carried its
own version would let one record contain two schema numbers that can disagree.

Consequence, and the point of the layout: **the wire bytes and the host
spelling are the same sequence.** `wire_to_hex(hash256_put([], d)) == d` for
every valid `d`.

### Why not four little-endian u64 halves

That is the shape `Hash128` uses (`hi: u64, lo: u64` through `wire_put_u64`),
so it is the obvious alternative. It is rejected because:

1. A digest is a **byte string**, not a number. `Hash128`'s halves are a
   number-shaped carrier and its own docstring has to warn that "a hash with
   the top bit set appears negative". At 256 bits there is no natural
   `hi`/`lo`; naming four halves would need an ordering convention with no
   source in the architecture text.
2. LE u64 halves reverse the spelling **inside each 8-byte group**, so the hex
   a human reads and the bytes on the wire differ. Two readings of one hash is
   the failure this contract exists to end.
3. PLACE already shipped raw bytes. Changing PLACE would be a wire change to a
   frozen contract and its lane owner's call (see *Raised for ratification*).

The ascending-ladder golden vector pins this: under LE halves it would encode
as `0706050403020100 0f0e0d0c0b0a0908 1716151413121110 1f1e1d1c1b1a1918`,
differing in 48 of 64 characters. **A round-trip test accepts either.** The
gate asserts the exact string and additionally asserts the LE-halves string is
*not* produced.

## Host spelling rules — frozen

- Exactly **64** characters.
- Alphabet **`0123456789abcdef`** only.
- **Uppercase is REJECTED, not folded.** Two spellings of one hash would give
  one record two encodings, and a receipt hashing that record would not be
  stable — which breaks §21's cross-mode determinism gate, whose whole premise
  is that receipts compare equal. This is the rule
  `placement_contracts/storage.spl` already imposes on an `ArtifactId` digest,
  restated here as the general rule.
- The empty text is **not** a digest.

## Absence

There is **no absence sentinel**, and `HASH256_ZERO` is deliberately not one.
The all-zero digest is a legal digest — some artifact hashes to it — so a
record that needs to express "no digest" MUST carry a separate presence flag,
exactly as §20.2's `deadline` does with `deadline_present`. Naming the zero
constant here, with that statement attached, is what stops a later lane from
quietly reusing it as a sentinel and making one value mean two things.

## Six deliverables

| # | Deliverable | Where |
|---|---|---|
| 1 | Binary schema | This document, *Layout*. SDN schema block: `test/fixtures/structural/hash256_golden_v1.sdn`, `contract:` section |
| 2 | Simple types | `src/lib/common/structural/digest/hash256.spl` (widths, alphabet, validation), `.../digest/__init__.spl` |
| 3 | Rust/C++ bridge types | Normative definitions below, mirrored in the `.sdn` `bridge_types:` block |
| 4 | CPU reference serializers | `src/lib/common/structural/digest/hash256_codec.spl` |
| 5 | Golden vectors | `test/fixtures/structural/hash256_golden_v1.{spl,sdn}` — exact-byte, hand-derived |
| 6 | Versioning policy | Below |

### 3. Rust / C++ bridge types

```rust
#[repr(C)]
pub struct Hash256(pub [u8; 32]);
```

```cpp
struct Hash256 { uint8_t bytes[32]; };
```

Both are plain 32-byte arrays with no padding, so `sizeof == 32` on every
supported target and the value may be `memcpy`'d into a record buffer at the
field offset with no per-field serializer. **Do not model this as four `u64`
halves** — on a little-endian host that reverses the spelling inside each
8-byte group.

Shipped as normative definitions rather than as source files, the same call
waves 0a, 0b and the RECEIPT lane made: no caller exists at this revision, and
the repository rule is that implementation code is `.spl`/`.shs`. The layout
above plus the `.sdn` vectors let the owning bridge lane build and validate an
encoder without linking Simple.

## 6. Compatibility and versioning policy

- `HASH256_LEN = 32`, `HASH256_HEX_LEN = 64`, the byte order, the alphabet and
  the case rule are **frozen** and are part of the contract of every record
  that embeds a `Hash256`.
- Because `Hash256` carries no version of its own, changing any of the above is
  a **schema-version bump of every embedding record** — not an additive change
  and not a local edit. That is the price of it being a field type, and it is
  the reason the width is pinned by an assertion in the gate rather than left
  implicit.
- The golden vectors are the contract. They are never edited in place; a change
  that alters them is a version bump.
- Widening the accepted spelling — accepting uppercase, accepting a shorter
  digest, accepting non-hex — is **breaking**, because the rejection vectors
  pin the accepted set from the outside. Narrowing it is breaking too.

## Raised for ratification

**H1 — the RECEIPT lane's `Hash256` fields do not use this encoding.**
`input_root`, `output_root` and `deterministic_hash` are u32-length-prefixed
ASCII text accepting any ASCII (`receipt_contract_v1.md` A2, which chose this
explicitly and flagged it as **R2**, "decide whether `StageId` / `BackendId` /
`Hash256` are names or numbers"). Aligning them to the 32-byte form is a wire
change to an already-frozen contract and is the RECEIPT lane owner's call.
**Reported, not done** — frozen enums and frozen layouts are closed. Note the
consequence if it is declined: two frozen contracts encode one named type
differently, permanently.

**H2 — PLACE should import these primitives instead of keeping its own.**
`placement_codec.spl` carries `place_hex_nibble` / `place_put_hash` /
`place_read_hash` and `PLACEMENT_HASH_LEN`, byte-identical in behaviour to the
functions frozen here. That duplication is harmless **today** precisely because
the layouts agree; it is a divergence waiting to happen the first time one side
is edited. Replacing them is a no-op on the wire and a real reduction in
surface, but it edits a frozen lane's file, so it is that lane's call.

**H3 — in-tree values that this contract refuses.** Real, currently-unmet
migrations, not theoretical ones:
- `src/lib/nogc_async_mut/gpu/placement_backends/staged_backend.spl` writes
  `Hash256(value: "staged_empty")`.
- `src/lib/common/structural/receipt/receipt_types.spl` initialises
  `input_hash: ""`, `output_hash: ""`, `deterministic_hash: ""`.
- `placement_backends/planner.spl` builds `Hash256(value: request_signature(…))`
  from a signature function with no stated 64-hex postcondition.

Each is pinned as a rejection vector so the migration cannot be forgotten.

**H4 — `MutationPlan.plan_hash` may now be 256-bit.** The MUTATE lane deviated
to `Hash128` *because* `Hash256` had no encoding
(`mutation_contract_v1.md` §4). That reason is now gone. Whether to take the
v2 bump the MUTATE lane already anticipated is its owner's call.

## Golden vectors

`test/fixtures/structural/hash256_golden_v1.spl` (Simple) and
`test/fixtures/structural/hash256_golden_v1.sdn` (language-neutral mirror).

Every hex string was derived **by hand from the layout table above**, not
captured from encoder output. The gate asserts encoder output EQUALS the
vector, which is the direction that catches a symmetric encode/decode defect —
a round trip alone passes one straight through.

Five value vectors (zero, ones, ascending ladder, descending ladder, high-bit),
one embedded-field vector (u32 then digest, 36 bytes), and seven rejection
vectors (uppercase, mixed case, 63-char, 66-char, non-hex, empty, free-form).

Gate: `test/01_unit/common/structural/hash256_contract_spec.spl`.

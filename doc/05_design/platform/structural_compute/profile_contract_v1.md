# Profile-descriptor contract v1 — ResolveProfile / SpatialLayoutProfile

Freezes §26 artifact group 11, "ResolveProfile and SpatialLayoutProfile
contracts". Normative sources: architecture §17.2/§17.3 (layout islands,
`SpatialLayoutProfile` interface, the eight initial layout profiles), §18.1/§18.2
(`ResolveProfile` interface, the core primitive list, the three initial resolve
profiles), §19 (SMF link stages L0–L12), §26, §27, Appendix A.

Code: `src/lib/common/structural/profile/`
Spec: `test/01_unit/common/structural/profile_contract_spec.spl`
Golden vectors: `test/fixtures/structural/profile_golden_v1.{spl,sdn}`

---

## 1. What is frozen, and what deliberately is not

The two *behavioural traits* named by §26 already existed before this freeze
and are owned by other lanes:

| Trait | File | Owning lane (§27) |
|---|---|---|
| `ResolveProfile` | `src/lib/common/structural/resolve/resolve_types.spl` | LINK |
| `SpatialLayoutProfile` | `src/lib/common/structural/layout/profile.spl` | LAYOUT |

Neither file is edited by this freeze — §27 gives those directories to LINK and
LAYOUT exclusively, and `src/lib/common/structural/__init__.spl` is a shared
integration file.

A trait is not a contract artifact. It has no bytes, so it cannot be versioned,
shipped across a language boundary, golden-tested, or rejected on receipt. §26
asks for "language-neutral binary/SDN schema … golden vectors … compatibility
policy", and what was missing is the *descriptor*: the record a producer emits
to declare which profile it is, which of the frozen interface steps it actually
implements, which core primitives it consumes, and which execution properties a
planner may rely on without invoking it.

This document freezes exactly that: `ResolveProfileDescriptor` and
`SpatialLayoutProfileDescriptor`.

### Types reused, not re-declared

`Hash128` comes from the frozen ID-TAG contract. This lane mints no identity
model, no execution-mode enum, and no receipt type. The wire primitives
(`wire_put_u8` … `wire_check_envelope`, `wire_to_hex`) are the shared ID-TAG
port in `src/lib/common/structural/wire.spl`.

The layout kind spellings and the per-kind GPU eligibility rule are *not* a new
vocabulary either: they are asserted equal to the LAYOUT lane's live
`LAYOUT_PROFILE_*` constants and `layout_profile_gpu_eligible` in the spec, so
the two cannot drift into two vocabularies for one concept.

---

## 2. Scalar convention

Inherited unchanged from the identity/tagmap contract: little-endian, fixed
width, no padding, no alignment; enums are a single `u8` discriminant; every
top-level record carries the 8-byte envelope `magic u32 | version u16 |
reserved u16 (== 0)`; writers mask to width; decoders are total and return an
`ok` flag; unknown discriminants and set reserved bits are HARD REJECTS, never
silent defaults.

Magics: `SRPD` (resolve profile descriptor), `SLPD` (spatial layout profile
descriptor). Schema version 1.

---

## 3. `ResolveProfileDescriptor` — 32 bytes

| off | size | field | type | notes |
|---|---|---|---|---|
| 0 | 16 | `profile_id` | `Hash128` | interned profile-name identity |
| 16 | 1 | `kind` | `u8` | `ResolveProfileKind` |
| 17 | 1 | `step_mask` | `u8` | `RESOLVE_STEP_*` |
| 18 | 2 | `core_mask` | `u16` | `RESOLVE_CORE_*` |
| 20 | 4 | `space_count` | `u32` | distinct `ResolveKey.space` namespaces |
| 24 | 4 | `stage_count` | `u32` | pipeline stages the profile reports |
| 28 | 4 | `reserved` | `u32` | MUST be 0 |

Framed length 40 bytes.

### `ResolveProfileKind` — closed, three values

`0 smf_link`, `1 clang_offload_link`, `2 web_resource_link`. §18.2 names exactly
these three. The vocabulary is closed because §18.2 states profiles "share
GraphResolveCore primitives, never semantics": a consumer that cannot name the
profile cannot know its resolution semantics, so an unrecognised kind must fail
rather than fall back.

### `step_mask` — one bit per §18.1 interface method, in declaration order

`collect 1`, `group_key 2`, `resolve_group 4`, `derive_constraints 8`,
`plan_placement 16`, `emit 32`. Bits 6–7 reserved, MUST be 0.

Mandatory set = `collect | group_key | resolve_group | emit` (39).
Derivation: the first three produce the resolution and `emit -> MutationPlanRef`
is the only externally observable output. `derive_constraints` and
`plan_placement` are genuinely optional — §18.2's `WebResourceLinkProfile` has
no address space to place into.

### `core_mask` — one bit per §18.1 "The core provides:" entry, in listed order

`hash/intern 1`, `stable sort/group 2`, `deterministic group reduction 4`,
`reachability frontiers 8`, `constraint propagation 16`, `scan-based placement
32`, `patch emission 64`, `receipts and diagnostics 128`. Bits 8–15 reserved,
MUST be 0.

Mandatory set = `hash/intern | stable sort/group | group reduction | receipts`
(135). The first three are what "resolve" means; receipts are unconditional
because §30 verification reads them for every stage.

### Cross-field invariants (enforced on encode **and** decode)

1. `derive_constraints` declared ⟺ `constraint propagation` declared.
2. `plan_placement` declared ⟺ `scan-based placement` declared.
3. `emit` lowers to `patch emission`, which is therefore always required.
4. `space_count ≥ 1` — a profile with no namespace can never form a `ResolveKey`.
5. `stage_count ≥ 1`.
6. `space_count + stage_count` must fit a `u32`. See §6.

---

## 4. `SpatialLayoutProfileDescriptor` — 24 bytes

| off | size | field | type | notes |
|---|---|---|---|---|
| 0 | 16 | `profile_id` | `Hash128` | interned profile-name identity |
| 16 | 1 | `kind` | `u8` | `SpatialLayoutProfileKind` |
| 17 | 1 | `step_mask` | `u8` | `LAYOUT_STEP_*` |
| 18 | 2 | `flags` | `u16` | `LAYOUT_FLAG_*` |
| 20 | 4 | `admission_mask` | `u32` | `LAYOUT_GPU_ADMISSION_*` exclusions |

Framed length 32 bytes. There is no trailing reserved word: `flags` and
`admission_mask` each carry their own reserved bits, hard-rejected when
nonzero, so a spare word would add four bytes of nothing to every descriptor.

### `SpatialLayoutProfileKind` — closed, eight values

`0 block`, `1 inline`, `2 flex`, `3 grid`, `4 table`, `5 absolute-sticky`,
`6 scroll`, `7 replaced`. Spellings are byte-identical to the LAYOUT lane's
`LAYOUT_PROFILE_*` constants and asserted equal in the spec.

### `step_mask` — one bit per §17.3 behavioural method

`discover 1`, `estimate 2`, `measure 4`, `arrange 8`, `verify 16`. Bits 5–7
reserved, MUST be 0. `profile_id()` is not a step; it is the descriptor's own
identity field.

Mandatory set = `discover | estimate | arrange` (11). `measure` runs only for
profiles that shape text; `verify` only where an oracle exists (§17.3 takes
`oracle: LayoutSnapshotRef?`).

### `flags`

`gpu_eligible 1`, `text_measure_required 2`, `sequential_within_island 4`.
Bits 3–15 reserved, MUST be 0.

### `admission_mask`

The nine-bit exclusion vocabulary already in use by the LAYOUT lane as
`LAYOUT_GPU_ADMISSION_*` (values 1…256). Bits 9–31 reserved, MUST be 0.

### Cross-field invariants (enforced on encode **and** decode)

1. `text_measure_required` ⟺ the `measure` step is declared. The flag exists so
   the scheduler can skip the text port; a flag disagreeing with the step set
   makes that skip unsound.
2. `gpu_eligible` must equal the frozen per-kind eligibility — `block`, `flex`,
   `grid`, `absolute-sticky`, `scroll`. Eligibility is a property of the
   formatting context, not of an individual descriptor, so a descriptor cannot
   opt an inline profile into GPU. Derivation: §29 Wave 8 ("block/flex/grid GPU
   batches", "CPU fallback for text/irregular contexts") and §17.2 (inline
   formatting is sequential within a paragraph). Asserted equal to the LAYOUT
   lane's `layout_profile_gpu_eligible` for all eight kinds.
3. `gpu_eligible` excludes `sequential_within_island`.
4. A profile that is not `gpu_eligible` declares no admission exclusions: it has
   no GPU admission decision to filter.

---

## 5. Encode-side enforcement — a deliberate divergence

The identity / mapping / resolve encoders return a bare `[u8]`, because their
records are near-free-form (any `u64` attribute bitset is legal). A profile
descriptor is almost entirely invariant-bearing, so the shared freeze rule
"enforce invariants on encode as well as decode" has real content here.

Both encoders therefore return `ProfileEncodeResult { ok, bytes }` and refuse to
emit bytes for a descriptor a conforming decoder would reject; `bytes` is empty
when `ok` is false, so no partial buffer can be mistaken for a record. An
ill-formed descriptor never reaches the wire, instead of failing on the far side
of a file or network boundary where the producer is already gone.

---

## 6. The 32-bit width trap, and why the usual fix does not work here

`space_count + stage_count` must fit a `u32`. The standing advice is "widen into
`i64` before comparing". **Measured in this tree, that is not sufficient.**

A helper `fn sum_probe(a: i64, b: i64) -> i64: val total: i64 = a + b` returns:

- `sum_probe(4294967295, 1)` → `4294967296` (correct)
- `sum_probe(d.space_count, d.stage_count)` holding the same values → `0`

The `u32` struct field's 32-bit width survives the `i64` parameter declaration
and the addition wraps to zero, so a wrapped total passes as well-formed. The
declared parameter type does not widen the value.

`resolve_profile_counts_valid` therefore **never forms the sum**. It bounds
`space_count` to `[1, U32_MAX]` first, then tests
`stage_count <= U32_MAX - space_count`. That subtraction cannot wrap at any
width once the bound holds.

This was caught by an exact-value assertion, not by round-tripping. Reported for
ratification: other frozen groups holding two `u32` fields that are summed
should re-check against this measurement rather than assuming the `i64`
parameter widens.

---

## 7. Golden vectors

Six vectors, hand-derived from the layout tables above and cross-checked against
an independent field-by-field derivation that does not call the Simple encoder;
they were **not** captured from encoder output.

`RPD_SMF`, `RPD_WEB` (the placement-free profile), `RPD_MAX` (u32 count width
witness), `LPD_BLOCK`, `LPD_INLINE` (sequential, CPU-only, text-measuring),
`LPD_GRID` (all steps, all admission bits). Bytes in
`test/fixtures/structural/profile_golden_v1.spl`, mirrored for other languages
in `profile_golden_v1.sdn`.

As with the resolve vectors, `u64` top-bit round-trip coverage lives in the
identity golden vectors; these use max-positive `u64`s.

**Non-vacuity evidence.** A symmetric encoder+decoder defect (swapping `kind`
and `step_mask` in both `_put` and `_read`) leaves all four round-trip examples
green and fails only the three exact-byte resolve examples: `38 total, 35
passed, 3 failed`, versus `38 total, 38 passed, 0 failed` before and after.
Round-trip testing alone cannot see this class of defect.

---

## 8. Compatibility and versioning policy

Identical to the sibling frozen contracts:

- Wire records are immutable. A field width, offset, order, or discriminant
  meaning never changes in place. Any change is `PROFILE_SCHEMA_VERSION = 2`
  plus a new `profile_golden_v2.{spl,sdn}`; `_v1` fixtures are never edited.
- `wire_check_envelope` rejects a version mismatch outright. Version is not
  negotiated (§12.6): a v1 decoder handed v2 bytes fails, it does not guess.
- Reserved bits and the reserved `u32` are the only forward-compatibility
  channel, and using one is a version bump: a v1 decoder hard-rejects any
  reserved bit set, exactly so that a v2 producer cannot be silently
  misinterpreted by a v1 consumer.
- The two kind vocabularies are closed. Adding a fourth resolve profile or a
  ninth layout profile is a version bump, not an additive change.
- Adding a step or core bit within the existing reserved range is likewise a
  version bump, because the mandatory-set and cross-field checks are part of
  the contract, not of any one implementation.
- The CPU reference codec is the oracle and is never deleted. Any future
  vectorized or GPU-resident encoder must produce byte-identical output.

### Rust / C++ bridge types

None are required at this freeze. The descriptors cross language boundaries as
the 40-byte and 32-byte frozen buffers, which any language can read with the
tables in §3 and §4; there is no in-memory layout to agree on, which is the
point of a fixed-width, unaligned, little-endian wire form. The `.sdn` mirror
carries the same bytes for consumers that prefer text. If a bridge lane later
needs a `#[repr(C)]` mirror, it is derived from these tables and validated
against the same golden vectors — it does not become a second source of truth.

---

## 9. Reported for ratification

**P1 — Appendix A lists seven layout profiles, §17.3 lists eight.** Appendix A's
implementor line reads "block, inline, flex, grid, table, positioned, scroll":
it drops `replaced` and spells `absolute/sticky` as `positioned`. §17.3 is the
normative list and the in-tree LAYOUT lane already implements eight. This
contract freezes §17.3's eight and treats Appendix A as prose shorthand.

**P2 — the `u32` sum trap of §6** may affect other frozen groups.

**P3 — `space_count` for `WebResourceLinkProfile` is read as 6** from §18.2's
list (stylesheet imports, URLs, fonts, keyframes, custom properties,
script/module/component resources). The list is prose; if the intent was to
group the last item, the golden vector value changes but no wire slot does.

**P4 — `SourceOriginSet` does not belong to this group.** It is the return type
of `MappingGraph::trace_to_source` (§14). No `ResolveProfile` or
`SpatialLayoutProfile` method mentions it, no field of either descriptor refers
to it, and §18.2 explicitly separates spatial layout from resolution. It remains
where the receipt freeze left it: ambiguous between MAP and QUERY. This group
does not absorb it.

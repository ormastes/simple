# Frozen contract v1 — CLANG-AST export, identity and adapter capability

**Date:** 2026-08-01 · **Status:** Frozen (wave 1, CPU reference) · **Lane:** CLANG-AST + LLVM

Normative parents (these win on any conflict):

- `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
  — §12 Clang bridge architecture, §12.2 Clang entity identity, §12.3 Clang AOP,
  §12.5 three-mode plan, §12.6 version and compatibility policy, §25 source
  placement, §26 contract freeze, §27 lane ownership.
- `doc/03_plan/platform/structural_compute/clang_bridge_plan.md` — lane plan.
- `doc/03_plan/platform/structural_compute/README.md` — shared lane rules.
- `doc/05_design/platform/structural_compute/identity_tagmap_contract_v1.md`
  — §2 CONVENTIONS, inherited unchanged.

This document freezes the CLANG-AST lane's phase-1 deliverable ("Pin +
export"). It does **not** freeze QueryIR, MutationIR, or the LLVM IR schema —
see §7.

---

## 1. Deliverables

| §26 deliverable | Where |
|---|---|
| Language-neutral binary/SDN schema | §3–§5 below, mirrored in `test/fixtures/structural/clang_golden_v1.sdn` |
| Simple types | `src/lib/common/structural/clang/clang_types.spl` |
| Rust/C++ bridge types | Not shipped — see §6 |
| CPU reference serializers/deserializers | `src/lib/common/structural/clang/clang_codec.spl` |
| Golden vectors | `test/fixtures/structural/clang_golden_v1.spl` (+ `.sdn`) |
| Compatibility/versioning policy | §8 |

Verification gate: `test/01_unit/common/structural/clang_contract_spec.spl`.

Shipped files:

```text
src/lib/common/structural/clang/__init__.spl      facade, explicit re-exports
src/lib/common/structural/clang/clang_types.spl   value types + predicates
src/lib/common/structural/clang/clang_codec.spl   CPU reference codec

test/fixtures/structural/clang_golden_v1.spl      golden vectors
test/fixtures/structural/clang_golden_v1.sdn      language-neutral mirror
test/01_unit/common/structural/clang_contract_spec.spl
```

Placement follows §25 (`src/lib/common/structural/<group>/`) and ID-TAG
conventions §2.1. No `FILE.md` manifest exists on these paths, so no manifest
entry was required, and no shared export, driver, CLI or MDSOC binding file was
touched — module resolution is path-based, so
`use std.common.structural.clang.{...}` resolves with no registry edit. This
respects the §27 shared-file rule and shared rule 2 (exclusive path ownership).

## 2. Inherited conventions

Byte-level conventions are **not** restated here. They are frozen in
`src/lib/common/structural/wire.spl` and stated normatively in
`identity_tagmap_contract_v1.md` §2.3: little-endian, fixed width, no padding,
no alignment; every enum is a single `u8` discriminant; every top-level record
carries the 8-byte envelope `magic u32 | version u16 | reserved u16 (== 0)`;
decoders are total and return an `ok` flag rather than an Option; an unknown
discriminant, a set reserved bit, or a version mismatch is a **hard reject**,
never a silent default.

`CLANG_SCHEMA_VERSION = 1`.

Absent ids are `0xffffffff`, matching the DrawIR v3 / GPU-web capacity
convention. Hot structures carry no text keys and no nested dynamic arrays.

## 3. Frozen layout — ClangEntityIdentity (§12.2)

Magic `SCEI`, 68-byte body, fields in the architecture's declaration order.

| Field | Bytes | Type |
|---|---|---|
| `tu_artifact` | 20 | `ArtifactId` |
| `ast_kind` | 4 | `u32` |
| `source` | 36 | `SourceAnchor` |
| `semantic_usr` | 4 | `u32` StringId, `0xffffffff` = absent |
| `local_ordinal` | 4 | `u32` |

`SourceAnchor` already carries `spelling_context` and `expansion_context` as
separate `u32` fields (ID-TAG §3), which is what §12.2's "macro entities
preserve spelling and expansion locations" requires; this lane adds nothing
there.

`semantic_usr` is spelled `StringId?` in §12.2. An Option is **not** put on the
wire — ID-TAG §2.3 rejects Option because its lowering differs across this
repo's execution engines. `0xffffffff` is unreachable as a real StringId (the
string arena would need 2^32 entries) so the sentinel is unambiguous. Note that
StringId `0` is *present*, not absent.

## 4. Frozen layout — ClangAdapterCapability (§12.6)

Magic `SCAP`, 14-byte body, fields in the architecture's declaration order:
`clang_major u16 | ast_export_schema u16 | matcher_adapter_version u16 |
transformer_adapter_version u16 | llvm_ir_schema u16 | supported_features u32`.

`CapabilitySet` is frozen as a `u32` bitset with one bit per §12.1 component:

| Bit | Value | Component |
|---|---|---|
| 0 | 1 | `simple-clang-export` |
| 1 | 2 | `simple-clang-query` |
| 2 | 4 | `simple-clang-transform` |
| 3 | 8 | `simple-llvm-pass` |
| 4 | 16 | `simple-clang-profile` |

Bits 5..31 are RESERVED and MUST be zero; a set reserved bit is a hard reject.

**Supported Clang majors: 16..19, primary 18.** This mirrors the range this
repo already builds and tests against in
`src/compiler/70.backend/backend/llvm_version.spl`. The value is restated in
this lane rather than imported, because `src/lib/common` must not depend on
`src/compiler` and that file belongs to a different lane. The accepted-major set
is wire-visible policy: moving it is a `CLANG_SCHEMA_VERSION` bump.

### 4.1 Acceptance is a decision with a reason receipt

Shared rule 4 forbids silent fallback. Reading an advertisement and accepting it
are therefore **separate steps**: `decode_clang_adapter_capability` succeeds on
any well-framed record including one from Clang 99, and
`clang_capability_decide(cap, required_features)` returns
`ClangCapabilityDecision(accepted, reason)`. A caller that drops to a different
adapter or to plain Clang records the reason instead of shrugging.

`ClangRejectReason` discriminants (append-only, never renumbered):
`Accepted` 0, `UnsupportedMajor` 1, `AstExportSchemaMismatch` 2,
`MatcherAdapterMissing` 3, `TransformerAdapterMissing` 4,
`LlvmIrSchemaMismatch` 5, `MissingRequiredFeature` 6, `UnknownFeatureBits` 7.

Check order is frozen: major first (an unknown major invalidates every other
field's meaning, §12.6), then reserved feature bits (an adapter from the future
is "unknown", not merely "lacking"), then export schema, then required
features, then the per-component adapter versions.

## 5. Frozen layout — ClangAstExport

Magic `SCAX`. The "canonical flat AST export" of §12, structure-of-arrays,
column-major on the wire so a C1/C2 consumer transfers one column without a
strided gather.

```text
envelope(8) | producer_clang_major u32 | tu_artifact ArtifactId 20
            | node_count u32
            | kind    u32 * n
            | parent  u32 * n
            | ordinal u32 * n
            | flags   u32 * n
            | usr     u32 * n
            | anchor  SourceAnchor(36) * n
```

Header after the envelope is 28 bytes; each node costs 56.

`ClangNodeFlags` is a `u32` bitset. Each bit cites the sentence that forces it:

| Bit | Value | Meaning | Source |
|---|---|---|---|
| 0 | 1 | `MACRO_EXPANSION` | §12.2 macro entities; §12.3 "macro definitions" |
| 1 | 2 | `IMPLICIT` | §12.2 "generated/implicit declarations are tagged" |
| 2 | 4 | `SYSTEM_HEADER` | §12.3 "system headers" |
| 3 | 8 | `GENERATED_FILE` | §12.3 "generated files" |
| 4 | 16 | `TEMPLATE_INSTANTIATION` | §12.3 "ambiguous instantiations" |
| 5 | 32 | `SYNTHETIC_ORIGIN` | §12.2 "receive synthetic origins" |

Bits 6..31 RESERVED, must be zero. `REWRITE_GUARDED = 29` (bits 0,2,3,4) is the
mask §12.3 requires an explicit policy for;
`clang_rewrite_policy_required(flags)` is the CPU-reference oracle for that
admission check. `IMPLICIT` and `SYNTHETIC_ORIGIN` are deliberately outside the
mask: neither is a source range, so there is nothing to rewrite and nothing to
decide.

### 5.1 Frozen structural invariants

Checked on encode **and** on decode, because a producer that emits a malformed
arena and a consumer that accepts one are two different failures:

- every column is exactly `node_count` long;
- `producer_clang_major` is in the supported set (§12.6);
- no `flags[i]` sets a reserved bit;
- `parent[i]` is either `0xffffffff` (root) or **strictly less than `i`**. The
  export is preorder, so a parent always precedes its children. This one check
  rules out self-parenting and every cycle, and it is the check that makes a
  corrupted arena fail loudly instead of silently reparenting a node — the same
  hazard the MAP lane guards in its CSR offsets;
- `node_count` consumes the buffer **exactly**; trailing bytes are a rejection.

An export with `node_count == 0` is **valid**, not an error: it is the canonical
result of exporting a translation unit with no nodes.

`encode_clang_ast_export` returns an **empty buffer** for a malformed arena. An
empty buffer fails the envelope check unambiguously, so the failure surfaces at
the first read rather than downstream.

### 5.2 Identity ↔ index

Arena indices are translation-unit-local, exactly as raw Clang pointers are.
The boundary rule from plan phase 2 — "captures return `EntityKey`, never
`Decl*`/`Stmt*`" — is enforced by exporting only:

- `clang_identity_of(export, i) -> ClangEntityIdentity` — the durable key;
- `clang_export_index_of(export, identity) -> i64` — canonical-index
  resolution, or `-1`.

`clang_export_index_of` is a linear scan **on purpose**: it is the CPU-reference
oracle (shared rule 3). The C1 hybrid mode replaces it with a hashed pre-index
and must agree with this result exactly.

## 6. C++ bridge — deliberately not shipped

§12.1 names five bridge components and §25 places them at
`tools/clang-bridge/{frontend,transformer,llvm_pass}`. Those are Clang/LLVM C++
plugin surfaces — `FrontendAction`, `PPCallbacks`, `ASTConsumer`,
`SourceManager`, `PassBuilder` — and **cannot be expressed in Simple**. This
repo's rules require implementation in `.spl` before C/Rust wiring, and the
owned-code scope excludes vendored LLVM/clang trees. No C++ source and no
C/C++ build step are added by this lane.

What the C++ side needs is provided instead: §3–§5 give the complete byte
layout and `clang_golden_v1.sdn` gives vectors to validate an independent
encoder against without linking Simple. Shipping an uncalled bridge would create
a second definition of the wire format that nothing exercises — the opposite of
what a freeze is for. This mirrors the ID-TAG lane's §6 decision exactly.

**This is a scoping decision for the architecture owner**, not something this
lane can resolve: phases 1's export *producer*, and all of phase 4, require a
native Clang/LLVM plugin.

## 7. Blocked — what this lane did NOT implement, and why

Shared rule 1: "No lane implements against unfrozen contracts."

| Plan phase | Blocked on | Evidence |
|---|---|---|
| 2 — Query (QueryIR → AST Matcher) | QueryIR bytecode and capture format, §26 group 4, owned by the QUERY lane | No `src/lib/common/structural/query/` at `origin/main` |
| 3 — Transform (MutationIR → Replacements) | MutationIR and conflict order, §26 group 5, owned by the MUTATE lane | No `src/lib/common/structural/mutation/` at `origin/main` |
| 4 — LLVM plugin | Native C++ (see §6) plus an unfrozen LLVM IR schema | — |
| 5 — C1/C2 modes | `gpu_mmu` lane (README dependency order); CPU-reference is wave-1 and does not wait | — |

Accordingly `clang_this_build_capability()` advertises
`matcher_adapter_version = 0`, `transformer_adapter_version = 0` and
`llvm_ir_schema = 0` — "absent", never "assume compatible" — and
`supported_features = AST_EXPORT` only. The `ClangRejectReason` variants for the
missing adapters are frozen now so that a future adapter slots in without a
schema bump.

The lane plan lists `ClangAdapterCapability` among its dependencies as if it
were external; it is not — §12.6 defines it and §27 gives it to this lane, so it
is frozen here.

## 8. Versioning and compatibility policy

1. **A version mismatch is a rejection, not a negotiation.** A decoder accepts
   exactly `CLANG_SCHEMA_VERSION`. There is no "ignore unknown trailing bytes"
   path.
2. **An unknown Clang major is a rejection, not an assumption** (§12.6). This
   applies both to `producer_clang_major` inside an export (hard decode reject)
   and to `clang_major` in a capability (decodes, then `UnsupportedMajor`).
3. **A frozen file is never edited in place.** Any change to a field, its order,
   its width, or an enum discriminant is a new schema version.
4. **Enum discriminants and flag bits are append-only.** A retired number is
   burned, never reused.
5. `ast_export_schema` / `matcher_adapter_version` /
   `transformer_adapter_version` / `llvm_ir_schema` version the **adapter
   surfaces** and move independently of `CLANG_SCHEMA_VERSION`, which versions
   the **encoding** — so a reader can distinguish "I do not understand this
   format" from "I understand it but not this adapter revision".
6. **Each version keeps its golden-vector file.** A change adds
   `clang_golden_v2.spl` and keeps v1.

## 9. Underspecified in §12 — raised, not silently guessed

Each item below is also flagged where it appears in code.

| # | Item | Ref | Gap | Resolution taken |
|---|---|---|---|---|
| 1 | `CapabilitySet` | §12.6 | Declared in `ClangAdapterCapability`, never defined | `u32` bitset, one bit per §12.1 component, reserved bits hard-reject. Mirrors the MAP lane's `MappingKindSet` choice |
| 2 | Parent identity | §12.2 | Prose says stmts/exprs identify by "source anchor, kind, **parent identity**, and ordinal", but the given struct has no parent field | Struct frozen **as given**; the parent link lives in `ClangAstExport.parent`, because parent is graph structure (§6 MappingGraph owns edges) while `ClangEntityIdentity` is the durable key that travels alone. `clang_identity_of` keeps it recoverable |
| 3 | Flat AST export record | §12 | "canonical flat AST export" is named in the pipeline and in §12.5 C1/C2, but never given a shape | SoA arena with six parallel `u32`/anchor columns, modelled on the §13.1 `DomArena` precedent |
| 4 | Node flag vocabulary | §12.2/§12.3 | The four rewrite-hazard categories and the two tagging categories are named in prose but never enumerated as a type | Six-bit `u32` bitset, one bit per named category, plus the `REWRITE_GUARDED` mask |
| 5 | "One supported Clang major" | plan vs §12.6 | The plan says pin one major; §12.6 says one *adapter per* supported major | §12.6 wins (normative parent). Range 16..19, primary 18 |
| 6 | `ast_kind` vocabulary | §12.2 | `ast_kind: u32` is opaque — Clang's `Decl::Kind`/`Stmt::StmtClass` are not stable across majors | Left opaque **on purpose**; it is only meaningful paired with `producer_clang_major`, which the export carries and validates. Ratifying a stable cross-major kind vocabulary is a follow-up |

**Recommended resolution:** ratify items 1–4 explicitly in §12, since the QUERY,
MUTATE and LLVM lanes will all consume them. Item 6 needs a decision before
phase 2, because a matcher adapter cannot be written against an opaque kind.

## 10. Verification status

See the lane report for the run transcript, the binary used, and the sentinel
result. The spec proves the three required things separately — exact bytes,
round trip, rejection — plus an empty-input case (`node_count == 0` encodes,
decodes, validates, and resolves nothing), per ID-TAG §2.5.

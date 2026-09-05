# Simple Production and Mission-Critical Robustness Plan

**Date:** 2026-07-27
**Status:** Research + normative plan. Claims in §1 audit pending repo verification (see §13 Verification Appendix).
**Companion plan:** `doc/03_plan/agent_tasks/mission_critical_robustness_parallel_agents_2026-07-27.md`

## Executive verdict

The repository already contains several useful foundations: nominal `newunit` types,
primitive-public-API linting, strictness profiles, borrow checking, pattern-match checks,
Lean generation, native SIMD backends, accelerator backends, and fail-closed
release-evidence scripts. However, these mechanisms are not yet sufficiently unified or
complete to support a general claim that Simple is "more robust than Rust."

The defensible target is narrower and stronger:

> Simple Mission-Critical Profile provides stronger, mechanically enforced domain typing,
> semantic traceability, proof coverage, and fail-closed code-generation guarantees than
> ordinary Rust for a declared and versioned certified subset.

For mission-critical comparison, ordinary Rust is not the only relevant baseline. Rust
requires programmers and library authors to uphold invariants around `unsafe` that the
compiler cannot verify. Ferrocene adds a formal language specification, safety manual,
known-problem handling, qualification material, traceability, and certified library
subsets. Simple must compare itself with both stable Rust and a safety-qualified Rust
toolchain such as Ferrocene.

Do not publish a blanket "safer than Rust" statement. Publish measurable claims:

- Zero primitive types in public and mission-critical state interfaces.
- Zero unreviewed unsafe, FFI, intrinsic, or representation boundaries.
- Zero admitted Lean proofs in the certified dependency closure.
- One stable semantic identifier for every requirement, API, diagnostic, proof, test, and generated instruction.
- No silent scalar or unsupported-instruction fallback.
- Reproducible compiler and proof artifacts with a complete trust manifest.
- A complete, version-pinned Rust feature assurance ledger.

---

## 1. Current repository audit

| Area | Existing foundation | Production blocker |
|------|--------------------|--------------------|
| Primitive API checking | AST lint checks functions and fields; `newunit` exists | Canonical primitive list omits `bool` despite its comment; reliable-profile path remains text-based and function-only |
| Boolean semantics | Separate `bare_bool` work exists | Rules split across lint engines; no single semantic rule for APIs, fields, aliases, callbacks, enum payloads, nested types |
| Enum evolution | Enums, generic enums, strong-enum concepts exist | Parser records variant names but skips payload metadata; safe wire/persistent enum evolution not a first-class contract |
| Source traceability | Flat AST arena IDs and spans exist | Arena indexes and line numbers are not stable semantic identities |
| Lean | Contract workflow, proof states, Lean backend, MIR translation exist | Type export, contract extraction, obligation extraction contain empty implementations; inter-block CFG mostly rejected |
| SIMD | NEON, AVX-512, SVE2, RVV implementation files exist | Coverage not generated from ISA specs; docs already drift from source tree |
| GPU | CUDA/HIP/OpenCL/Metal/WebGPU/Vulkan orchestration exists | Portable value types narrow, PTX version stale, some CUDA lowering assumes 8-byte fields/elements |
| Mission-critical evidence | SimpleOS uses evidence tiers, prerequisite checks, formal gates, stale-evidence detection, fail-closed wrappers | Assurance model not generalized to compiler, language, stdlib, Lean translator, code generators |

Key inconsistencies to verify and fix first:

- The primitive lint's own description lists `bool`, but the implemented primitive table
  includes only integer and floating-point types. Generated spec audits `bool` while
  deliberately not counting it as a primitive-API violation.
- The newer reliable-profile implementation is text-based, excludes `bool`, covers only
  public functions, and leaves the semantic implementation unfinished. The EasyFix
  implementation scans text rather than resolved types; its "replacement" preserves the
  original line instead of performing a real migration.
- Current strictness documentation correctly avoids claiming the reliable tier is a
  monolithic safety guarantee. Keep that cautious wording until the new assurance gates
  are executable.

---

## 2. Mission-critical assurance profile

**Profile naming (2026-07-28):** Profile ladder renamed to moderate (unchanged), strict (formerly lib), robust (formerly reliable), critical (formerly mission-critical). Old spellings are deprecated aliases (warn once); see `doc/02_requirements/language/mission_critical_profile.md` § Profile ladder rename.

Keep moderate/strict/robust tiers. Add a stronger, versioned profile whose rules are
release requirements, not optional diagnostics:

```sdn
(assurance
  profile: "mission-critical-v1"

  warnings: "deny"
  primitive_public_api: "deny"
  primitive_state_fields: "deny"
  primitive_type_graph: "recursive"

  unsafe_boundary: "reviewed-only"
  ffi_boundary: "manifest-required"
  representation_boundary: "manifest-required"

  exhaustive_closed_enum: "deny"
  unchecked_enum_decode: "deny"

  lean_required: true
  lean_admitted: "deny"
  lean_trusted: "manifest-required"
  lean_coverage: "public-certified-closure"

  semantic_source_links: "required"
  line_source_links: "deny"

  unsupported_codegen: "deny"
  unverified_instruction: "deny"
  silent_acceleration_fallback: "deny"

  reference_mutability: "const-default"   # params/refs immutable unless `mut`; warn now, deny at profile v2
  reproducible_build: true
  evidence_freshness: "required"
  known_problem_register: "required")
```

The profile is fail-closed:

- If only the text scanner is available (semantic compiler cannot run), the mission-critical build fails.
- If Lean, a solver, an assembler validator, or other required tool is missing, the gate reports **blocked**, not passed.
- If an instruction has no verified lowering, compilation fails rather than silently selecting scalar.
- If proof or test evidence is stale relative to source/toolchain/spec versions, release is blocked.

This follows the existing SimpleOS evidence principle: generated artifacts are not
automatically proofs, host simulation is not hardware evidence, missing formal tools are
blockers.

---

## 3. Requirement 1: no primitive types in public and mission-critical interfaces

### 3.1 Semantic rule

The authoritative checker operates after name resolution and type normalization — never
on source strings. A violation exists when a primitive leaf is reachable through the
normalized type graph.

```simple
# Violation
pub fn connect(port: u16) -> bool

# Still a violation: aliases/containers cannot hide primitives
type PortAlias = u16
pub fn connect(port: PortAlias) -> Option<bool>

# Valid
newunit Port: u16
enum ConnectResult:
    Connected
    Refused
    TimedOut

pub fn connect(port: Port) -> ConnectResult
```

The recursive checker inspects: function/method parameters; return and error types;
constructor and callback signatures; trait requirements and associated functions; public
function-pointer and closure types; exported constants and statics; struct/class fields;
enum and tagged-union payloads; type aliases and reexports; tuple/array/collection/
Option/Result/generic arguments; generic defaults and public constraints; persisted,
serialized, shared-memory, hardware-register, and wire-format state.

`Option<i32>` is not safe merely because it is wrapped. `Option<RetryCount>` is.

### 3.2 Member-variable policy

- **Reliable profile:** reject primitive fields that are public or externally constructible.
- **Mission-critical profile:** reject primitive fields in all production-domain types,
  including private state, except inside an explicit representation boundary
  (`newunit` backing storage, FFI layout types, hardware register definitions, ISA
  encoder/decoder structures, serialization codecs, compiler prelude/runtime types).

Boundaries carry reason + review metadata:

```simple
@representation_boundary(
    reason: "NVMe command ABI field",
    standard: "NVM Express command layout",
    reviewer: "storage-safety",
    expires: "never")
struct NvmeRawCommand:
    opcode: u8
    namespace_id: u32
```

Ordinary application structs cannot use this annotation to silence the checker.

### 3.3 Remove unsafe exemptions

- The `_all_same_primitive` exemption (mathematical APIs) must not apply to the
  mission-critical profile. Mathematical APIs use a semantic scalar (Probability,
  Radians, BlockCount, NormalizedValue), a vector/matrix/complex/unit/tensor type, or an
  explicitly reviewed low-level numeric boundary module.
- `extern fn` is not simply skipped: the raw ABI signature may contain primitives, but
  the public Simple-facing API must be a generated, checked semantic wrapper.

### 3.4 Migration stages

| Stage | Normal builds | Robust (formerly reliable) | Critical (formerly mission-critical) |
|-------|---------------|----------|------------------|
| A: inventory | Audit report only | Warning | Error |
| B: migration | Warning + suggested wrappers | Warning | Error |
| C: freeze | New violations error; semantic baseline allowed | Error | Error |
| D: cleanup | Baseline must decrease | Error | Error |
| E: next edition | All violations error | Error | Error |

The baseline is keyed by semantic Symbol ID + normalized signature, not filename+line.
Auto-fixes are classified: machine-applicable (known wrapper exists), skeleton generation
(developer names the domain), diagnostic-only. The tool never invents that an integer
means bytes/milliseconds/sectors/retries/identifiers.

---

## 4. Custom boolean and evolvable enum design

### 4.1 Prefer domain enums over `newunit X: bool`

```simple
@condition(false: Disabled, true: Enabled)
enum FeatureEnabled:
    Disabled
    Enabled
```

`@condition` is compiler-known and allowed only in condition contexts (`if enabled:`).
It creates no general implicit conversion to/from `bool`. Annotation preferred over a new
keyword; optional later sugar `flag FeatureEnabled:` desugars to the annotated enum.

### 4.2 Safe evolution

Adding a third variant revokes implicit condition use: existing `if state:` becomes an
error with an automatic `match` rewrite suggestion. A new state never silently becomes
true or false.

### 4.3 Closed and evolving enums

**Closed** (`@closed`): exhaustive matches required; wildcard arms may be prohibited in
mission-critical code; adding a variant is a breaking change; invalid discriminants
rejected during decode.

**Evolving** (`@evolving(repr: u8, unknown: Unknown)`): unknown numeric values preserved
and round-trippable; downstream must handle `Unknown`; adding a known variant is
source-compatible; decode never constructs invalid bit patterns; reserved values recorded
in type metadata. Rust's `#[non_exhaustive]` is precedent, but wire/persistent enums need
the round-trip guarantee too.

**Prerequisite:** fix enum metadata — parser currently skips variant payload details.

---

## 5. Requirement 2: stable AST-based Markdown links

### 5.1 Two identities

- `NodeId`: compilation-local arena index (unstable, internal only).
- `SymbolId`: stable semantic declaration identity — 128-bit hash of schema version,
  package identity, module path, namespace, item kind, owner SymbolId, normalized
  declaration path, normalized public signature, generic arity + constraints.
  Excludes line/column, byte offset, doc text, function body, arena index.

Precedents: Rust `DefPathHash` and owner-relative HIR IDs; rustdoc intra-doc links; SCIP.

### 5.2 Link syntax

```
spl://ormastes.simple/compiler.frontend.parser#fn:parse_module~A3K9M7R2Y1Q8   (canonical)
spl:fn@compiler.frontend.parser.parse_module~A3K9M7R2Y1Q8                     (short)
```

Kind disambiguators: `fn@ method@ type@ trait@ field@ variant@ const@ contract@ test@`.
Short fingerprint is package-scoped; index retains full 128-bit value and rejects
short-form collision rather than guessing.

### 5.3 Linkable nodes

Modules, types, functions/methods, fields, enum variants, trait requirements, constants,
contract clauses, named proof obligations, named tests/scenario steps. Anonymous
expressions get no permanent links; use a named region: `@trace("wal.commit-record")`.

### 5.4 Tooling — LSP + lint + refactor must all handle .md links

Library `std.tooling.semantic_link` + commands:

```
simple ast-link from-line src/storage/wal.spl#L120-L136
simple ast-link resolve 'spl:fn@storage.wal.append_commit~...'
simple doc check-links
simple doc fix-links
```

Resolution: parse link → load correct revision → parse+resolve file → interval index over
semantic-node spans → rank (exact decl start, smallest containing node, enclosing owner)
→ emit only when unique; report ambiguity without modifying the document.

Integration requirements (all three tools share one resolver library):

- **LSP:** definition/hover/references work *from inside .md files* on `spl:` links;
  rename emits redirect entries old-SymbolId → new-SymbolId; broken links surface as
  diagnostics in the editor.
- **Lint:** `W-DOC-AST-001 line_based_simple_source_link` detects `src/foo.spl:42`,
  `#L42`, `#L42-L50`, GitHub `.spl` `#L...` links. Warn+fix initially → deny in
  mission-critical → deny by default next doc edition. Reviewed exception only for
  transient diff/forensics docs.
- **Refactor:** rename tooling rewrites `.md` semantic links atomically with source;
  ambiguous rename = broken-link error, never silent retargeting to a similar name.

### 5.5 Open research items (md-link)

- Fingerprint stability vs signature evolution: a deliberate signature change must break
  the link loudly (that is the feature), but a rename must redirect. Redirect table lives
  in the semantic index, is versioned, and is consulted by lint's fixer.
- Doc files outside the repo (wikis, issues): canonical `spl://` form carries package
  identity so external resolvers can work; short form is repo-local only.
- Incremental index: LSP must not reparse the world per keystroke; the semantic index is
  built at build/lint time and consumed read-only by LSP with mtime invalidation.

---

## 6. Requirement 3: close the Lean generation gap

### 6.1 Current gaps

Lean backend: deterministic module export, but type export empty, contracts synthesized
empty, obligation extraction returns nothing. MIR translator fails closed but accepts only
straight-line control flow (no goto/branch/switch). Two partially separate systems —
contract-driven gen-lean (visible sorry debt) and MIR-driven translation (rejects
unsupported) — must share one semantic model, proof inventory, trust model, status
vocabulary.

### 6.2 Verification IR

```
Simple AST/HIR → resolved types/effects → Verification IR → checked Lean AST → Lean source → Lean kernel → proof result + trust manifest
```

V-IR contents: `VType` (structs, enums, newunits, arrays, bitvectors, references),
`VExpr`, `VState`, `VCfg`, `VContract` (requires/ensures/modifies/invariant/decreases),
`VEffect`, `VObligation`, `VTrust`, `VSource` (SymbolId + span). No scattered text
concatenation.

### 6.3 Machine semantics

`BitVec 8/16/32/64` for machine ints; explicit checked/wrapping/saturating/overflowing
ops; stated floating-point model (IEEE-oriented formal model, bit-precise external
theory, declared trusted primitive with bounded use, or exclusion from first certified
subset — never silent real-number arithmetic); explicit bounds, error/panic semantics,
pre/post state for mutation.

### 6.4 Required obligations

Bounds; overflow per arithmetic mode; div/mod by zero; shift range; valid enum
discriminants; newunit/constructor invariants; match exhaustiveness; optional handling;
borrow/alias/lifetime assumptions; call preconditions; postconditions; loop invariants +
termination; FFI/hardware-boundary assumptions; accelerator lowering preconditions.
Aeneas (borrow-aware functional translation), Creusot (contract obligations), Kani
(bounded checking) inform the architecture; they are not substitutes for one coherent
Simple semantics.

### 6.5 Certified-profile rules

`sorry`/`admit` are errors; generated axioms are errors; `@trusted` only via signed trust
manifest; unsupported constructs are compile errors with source SymbolId; per-symbol
proof status; generated vs manual Lean files separated; regeneration never overwrites
manual proofs; theorem names reference SymbolId; proof cache keyed on source semantics +
generated Lean + deps + Lean version + libraries + trust-manifest version. Existing proof
states (verified/failed/admitted/trusted/stale/not-checked) are a good foundation;
mission-critical aggregate treats admitted, trusted-without-manifest, stale, not-checked
as release blockers.

### 6.6 Implementation sequence

1. Unify proof inventory/diagnostics/status between gen-lean and MIR Lean codegen.
2. Complete type export. 3. Contract extraction. 4. Obligation extraction.
5. Structured conditional control flow. 6. Loops with mandatory invariants + decreases.
7. Calls and recursion. 8. Arrays/slices/Option/Result/enums/newunits.
9. Explicit mutable-state translation. 10. Borrow/alias assumptions and proofs.
11. Translation validation + intentionally-faulty compiler tests.
12. File-level → symbol-level proof units.

Concurrency, lock freedom, scheduler fairness, hardware memory models: separate declared
proof domains, not hidden in the first backend claim.

---

## 7. Requirement 4: SIMD and GPU instruction coverage

### 7.1 Four levels

1. **Catalogued** — every instruction in a pinned spec has a registry row.
2. **Callable** — Simple exposes it with checked operands + feature requirements.
3. **Lowered** — native/LLVM/library/synthesized implementation exists.
4. **Certified** — encoding and semantics have required evidence.

Hand-written lists can never stay complete (SVE/SME growth, RVV intrinsics, AVX10.2,
current PTX, SPIR-V registries).

### 7.2 ISA registry

`spec/isa/{x86,arm,riscv,ptx,spirv,amdgpu}.sdn`, e.g.:

```sdn
(isa_operation
  id: "x86.avx10.vaddps.zmm"
  spec_version: "intel-sdm-2026-06"
  semantic_op: "vector.add"
  element: "f32"  shape: "fixed-16"
  required_features: ["avx10.2-512"]
  lowering: "native"
  encoder: "x86.avx10.encode_vaddps"
  decoder: "x86.decode_evex"
  fallback: "forbidden"
  verification: ["byte-golden", "decode-roundtrip", "llvm-mc-diff", "intel-sde", "hardware"])
```

Statuses per op/type/target: `native | synthesized | library | llvm | unsupported |
unverified` — the last two visible in docs and fatal in mission-critical builds.

### 7.3 Unified accelerated IR

Types: `FixedVector<T,N>`, `ScalableVector<T,MinN>`, `Mask<N>`, `ScalableMask`,
`MatrixTile<T,M,N,K>`, `SubgroupValue<T>`. Operation families: load/store/gather/scatter;
arithmetic + fused; compare/select/masks; shuffle/permute/compress/expand; reduction/
scan; widening/narrowing/saturation/conversion; dot-product + matmul; crypto/polynomial;
atomics + fences; subgroup/warp communication. Each op carries signedness, rounding,
overflow mode, NaN/FP-exception policy, mask merge/zero, tail policy, alignment, memory
ordering, VL semantics, feature requirements. SVE/RVV scalable vectors are not "wider
AVX".

### 7.4 Priorities

- **x86:** SSE→AVX-512 semantic coverage; AVX10 versioned caps; AMX tile state +
  save/restore; APX interactions; crypto/VNNI/GFNI/SHA separated.
- **Arm:** complete NEON; MVE/Helium; SVE/SVE2 scalable semantics; SME/SME2 streaming +
  ZA state; OS context-switch requirements for scalable/matrix state.
- **RISC-V:** RVV 1.0 complete; VL/SEW/LMUL/mask/tail/rounding modeled; Zve subsets;
  Zvk* crypto; vsetvl placement verified; register-group overlap prevented.
- **GPU:** PTX scalar/vector/subgroup/tensor; SPIR-V capabilities; AMDGPU/ROCm; Vulkan/
  OpenCL/WebGPU subgroup + cooperative matrix; explicit memory scope/order.

### 7.5 Concrete GPU blockers (fix before expanding coverage)

- Portable GPU layer exposes only U32/F32 value types.
- Pure-Simple PTX builder hardcodes `.version 7.8` (stale).
- CUDA lowering: fixed 8-byte field offsets, 8-byte loads/stores, cast source assumed
  i64, GEP assumes 8-byte elements → replace with canonical layout engine + resolved MIR
  types.
- GPU intrinsic registry is name-string driven and previously misclassified ordinary
  calls via optional-to-bool coercion → structural intrinsic IDs + typed signatures
  before adding hundreds of ops.

### 7.6 Certification testing per instruction row

Encoder byte golden; decoder round-trip; differential assembly vs LLVM/official
assembler; disassembler validation; operand/immediate fuzzing; semantic differential
execution; vendor emulator (Intel SDE, Arm emulation, RISC-V emulation); real-hardware
sampling; cross-backend numerical comparison; negative tests for unsupported feature
selection; OS-context-state tests for SVE/SME/AMX. "LLVM-supported" and
"Simple-native-certified" stay separate statuses.

---

## 8. Complete Rust feature comparison ledger

Prose cannot reliably "check every Rust feature." Build a version-pinned machine-readable
ledger from the Rust Reference + Ferrocene Language Specification:
`doc/08_tracking/rust_feature_assurance.sdn`.

```sdn
(rust_feature
  source_id: "FLS:<section-id>"
  rust_version: "<pinned-version>"
  feature: "unsafe raw pointer dereference"
  simple_equivalent: "raw_pointer_deref"
  syntax_status: "implemented"
  semantic_status: "different"
  safety_delta: "Simple mission profile requires reviewed boundary"
  mission_rule: "unsafe_boundary_without_contract"
  tests: ["..."]  proofs: ["..."]  known_gaps: []
  owner: "language-safety"  evidence_hash: "...")
```

Comparison results: `stronger | equivalent | weaker | different | intentionally-rejected
| not-implemented | unknown`. "Stronger"/"equivalent" require executable evidence;
undocumented rows are `unknown`.

Feature families to cover: language versions/editions; modules/visibility; primitive +
compound types; generics; traits/coherence; ownership/borrows/lifetimes; interior
mutability; unsafe (raw pointers, unions, transmute); pattern matching/exhaustiveness/
non_exhaustive; closures/captures; errors (Result/panic/unwind/abort); const evaluation;
async (pinning, cancellation); concurrency (atomics, orderings, Send/Sync); ABI/layout/
repr/FFI; macros; SIMD/intrinsics/target features; standard library subset; tooling;
unstable/nightly (explicitly rejected or tracked, never silently accepted).

CI fails when: a pinned Reference/FLS section has no row; a row lacks owner/evidence; a
stronger/equivalent claim lacks tests or proof; pinned version changes without re-audit;
a Simple feature exists in the compiler but not in the ledger; a known limitation is
removed without evidence.

---

## 9. Required document structure

| Path | Purpose |
|------|---------|
| `doc/01_research/language/simple_vs_rust_mission_critical_2026-07-27.md` | This document |
| `doc/02_requirements/language/mission_critical_profile.md` | Normative assurance-profile requirements |
| `doc/02_requirements/language/semantic_public_types.md` | Primitive prohibition + boundary exceptions |
| `doc/02_requirements/tooling/semantic_source_links.md` | Stable link requirements |
| `doc/04_architecture/compiler/semantic_symbol_id.md` | SymbolId + index architecture |
| `doc/04_architecture/compiler/verification_ir.md` | Verification IR semantics |
| `doc/04_architecture/compiler/lean_translation.md` | Lean translation + trust model |
| `doc/04_architecture/compiler/isa_registry.md` | Machine-readable ISA coverage architecture |
| `doc/05_design/language/condition_and_evolving_enum.md` | Custom boolean + enum evolution design |
| `doc/05_design/compiler/mission_critical_release_gate.md` | Aggregate compiler/toolchain gate |
| `doc/08_tracking/rust_feature_assurance.sdn` | Rust feature ledger |
| `doc/08_tracking/isa_coverage.sdn` | Generated ISA coverage status |
| `doc/08_tracking/lean_semantic_coverage.sdn` | Symbol-level proof coverage |
| `SAFETY_MANUAL.md` | User obligations, permitted subset, tool assumptions |
| `KNOWN_PROBLEMS.md` | Versioned known-problem register |
| `QUALIFICATION_PLAN.md` | Tool qualification + evidence plan |
| `ASSURANCE_CASE.md` | Claims, arguments, evidence, remaining assumptions |

Architecture/spec docs use semantic links. Dated reports may use line links only when
explicitly marked transient.

---

## 10. Release acceptance criteria

**Public semantic types:** zero primitive leaves in public certified type closure; zero
primitive state fields outside approved boundaries; `bool` covered by the same semantic
engine; aliases/reexports/payloads/callbacks/nested generics covered; semantic and
bootstrap compilers emit equivalent diagnostics; migration baseline empty for certified
modules.

**Semantic source links:** zero maintained `.spl#L...` links; every semantic link
resolves against the pinned revision; line insertion before a declaration does not alter
its link; ambiguous links never auto-rewritten; rename redirects explicit and tested;
deleted/changed symbols produce deterministic diagnostics.

**Lean:** no empty export paths; certified control-flow forms supported; unsupported
constructs fail compilation; every certified public symbol has proof status; zero
sorry/admit/undeclared axioms in the certified closure; trusted assumptions in the
release trust manifest; deliberately incorrect translations detected by validation tests.

**ISA/GPU:** every pinned-spec instruction has a registry row; every row has explicit
lowering + verification status; no silent fallback; feature detection tested; certified
native encodings pass encode/decode + assembler differential; stateful extensions include
OS save/restore requirements; layout-sensitive GPU lowering uses the canonical layout
engine; artifact manifests carry ISA/feature/compiler/registry/proof versions.

**Rust ledger:** every pinned section represented; every claim classified; stronger/
equivalent rows have executable evidence; weaker/unsupported areas public; toolchain
version changes invalidate stale rows.

**Release process:** reproducible artifacts; SBOM + dependency hashes; bootstrap
evidence; fresh proof/conformance evidence; known-problem review; tool qualification
report; complete trust manifest; aggregate gate fails closed on missing fields/tools/
stale reports.

---

## 11. Recommended implementation order

1. Mission-critical requirements + assurance terminology.
2. Fix the `bool` contradiction in the canonical primitive checker.
3. Replace the authoritative text scanner with resolved-type-graph checking.
4. Semantic baselines + deny-new-violation migration.
5. Stabilize enum payload metadata.
6. `@condition`, closed enums, evolving enums.
7. SymbolId + semantic source index.
8. Line-to-AST conversion + Markdown linting (LSP/lint/refactor integration).
9. Verification IR + unify the two Lean workflows.
10. Lean types, contracts, obligations, structured branches.
11. ISA registry + generated coverage reports.
12. Correct PTX versioning + CUDA layout assumptions.
13. Fan out architecture-specific ISA work.
14. Complete Rust feature assurance ledger.
15. Compiler-wide mission-critical release gate.

First merge batch: contract-lock, documentation-truth, canonical primitive checker,
semantic identity foundation. Broad backend work only after shared contracts freeze.

---

## 12. Additional robustness features to evaluate (beyond the four requirements)

Candidates surfaced during research; each needs its own verification pass before
adoption:

- **Effect typing for panic/allocation/IO** in the certified subset (Simple already has
  tier separation nogc/gc, sync/async — formalize it as checked effects).
- **Deterministic replay harness** for the interpreter/JIT divergence problem (the
  A/B-engines landmine): mission-critical builds run dual-engine differential execution
  as a gate, since neither engine is currently trustworthy alone.
- **Numeric range/unit refinement on newunit** (`newunit Port: u16 in 1..=65535`) so
  constructor invariants become Lean obligations automatically.
- **ABI freeze files** per certified module (like `cargo public-api` / abi-checker) so
  signature drift is a diffable artifact.
- **Fault-injection lint tier**: deliberate false-green injection as a standing CI lane,
  not only a wave-4 red-team activity.
- **Const-by-default references in the certified subset — ADOPTED (user decision
  2026-07-28)**: parameters and references are immutable by default in MC-profile code;
  mutation requires the existing `mut` parameter annotation (`fn f(mut buf: [i32])`) or
  a `me` receiver. Today only method receivers are const-by-default; collections are
  mutable by default (Decision #3); reference capabilities remain
  Planned-not-implemented. **Phasing: lint WARNING now (all tiers), escalating to
  deny/error in mission-critical at profile v2.** Rule ID `W-MC-REF-001`
  (unannotated-parameter mutation).

## 13. Verification appendix (repo ground truth, agent-verified 2026-07-27/28)

> Research-paper-style claims are often wrong about the actual tree. Every §1 audit claim
> was verified by four parallel agents against current source. Verdicts and evidence
> below; falsified premises are re-scoped, not silently kept.

### 13.1 Primitive lint / bool / profiles — ALL CLAIMS TRUE

- **bool contradiction TRUE:** `src/compiler/35.semantics/lint/primitive_api.spl:3`
  header lists bool; `BARE_PRIMITIVES` at `:20` omits it. There are **3+ divergent
  primitive tables**: Rust lint `src/compiler_rust/compiler/src/lint/rules.rs:6-8`
  includes bool; arena checker `primitive_api_arena.spl:35-38` includes bool; the
  semantic `.spl` checker and both text lints exclude it.
- **Text-based reliable path TRUE:** `src/app/cli/query_lint.spl:99-162` — string
  scanning, `pub fn`/`pub me`/`pub static fn` only, no fields, bails on any
  generic/array/tuple return (`:117-119`), no bool. Profiles live at
  `src/compiler/90.tools/lint/_LintMain/config_and_model.spl:43-57,151-175`
  (Reliable → `primitive_api="deny"` at `:166`). **No `.sdn` in-repo actually sets
  `[lints] profile=`** — the profile machinery is effectively unexercised.
- **EasyFix no-op TRUE:** `src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl:128-151`
  emits `Replacement.create(... new_text: line)` — the original line, unchanged.
  `_all_same_primitive` math exemption at `:158-167` (Rust mirror
  `checker_core.rs:120-145`).
- **extern fn skipped everywhere TRUE:** text paths gate on `is_extern_fn`
  (`lint_primitive_api.spl:40-42,102-104`; `query_lint.spl:130,133`); Rust AST path
  never routes `Node::Extern` to `check_function` (`checker_core.rs:376,437-513`).
- **newunit: parser-complete, semantics is a stub.** Parser registers the type
  (`_ParserDecls/enum_module_body.spl:630-653`), but the unit registry is an
  **intentional scaffold** — `src/compiler/30.types/units/unit_registry.spl:253-282`
  never collects newunit declarations. Bonus bug: the fixer suggests `newtype ...`
  (nonexistent keyword) at `primitive_classification.spl:86`.

### 13.2 Lean gaps — CLAIMS TRUE (with one correction)

- Type export stub: `src/compiler/70.backend/backend/lean_backend.spl:351-356`.
  Contracts always empty: `:400` `FunctionContract.empty`. Obligations: `:405-409` is
  `pass`; `VerificationCodegen.generate_proof_obligations:591-593` returns `[]`.
- MIR translator fails closed and rejects ALL inter-block flow:
  `lean_mir_translate.spl:232-261` — Goto/If/Switch/CallTerminator all `Err`; only
  Ret/Unreachable/Abort succeed.
- Proof-state model exists: `src/compiler_rust/lib/std/src/verification/state.spl:12-18`
  (Verified|Failed|Admitted|Trusted|Stale|NotChecked, worst-case aggregation `:60-87`).
- Two separate systems confirmed in different trees: contract-driven
  (`src/compiler_rust/lib/std/src/verification/lean/contracts.spl:42,149,165,185` —
  emits `sorry`) vs MIR-driven (`src/compiler/70.backend/`, refuses `sorry` at
  `lean_backend.spl:556-560`).
- **Correction to the plan's tone:** checked-in Lean is already clean — 38 projects, 99
  `.lean` files under `src/verification/`, **0 actual sorry/admit/top-level axiom**
  (35 grep hits are prose comments). But the gate's `_count_sorry`
  (`src/compiler/90.tools/verify/checker.spl:246-254`) is a substring test that would
  false-positive those comments — fix as part of C6.

### 13.3 md-link tooling inventory (lane B ground truth)

- **LSP** (`src/app/lsp/`): definition/references/hover/completion/symbols/
  semanticTokens/implementation/codeAction/callHierarchy supported
  (`render_adapter.spl:53-62`). **No rename, no prepareRename, no markdown handling.**
- **`query rename` is grep+sed**, not semantic (`src/app/cli/query_navigation.spl:14`):
  scans only `src/**/*.spl` — **markdown never updated on rename**. This is exactly the
  gap.
- **Lint already walks `.md`**: `_LintMain/lint_checks.spl:645`
  `check_stale_md_diagrams` — the natural hook for `W-DOC-AST-001`.
- Only real md-link checker: `src/app/llm_process_gen/main.spl:620 check_links` — it
  **strips `#` fragments** and would skip/reject `spl:` URIs today (`:646
  should_check_link`).
- Only in-place md rewriter precedent: `src/app/md_diagram_update/main.spl`.
- **No stable symbol-ID infrastructure exists.** HIR `SymbolId` is a compile-local
  integer explicitly documented unstable (`src/compiler/70.backend/backend/env.spl:25-29`).
  Fingerprint precedent: `llm_process_gen`'s `source_sha256` markers.
- Naming collision to avoid: `bin/simple check-links` is **linker** dep resolution
  (`src/app/cli/check_links.spl`) — the doc command must use a different name
  (`simple doc check-links` as planned).

### 13.4 Enum / AST / SIMD / GPU — ALL CLAIMS TRUE

- Enum payloads parsed then discarded: `parser_decls_types.spl:122-149` ("Skip
  field_name: type pairs"), only names reach `decl_enum_def` (`_Ast/decl_nodes.spl:586`).
- Flat arena + i64 indices + span side tables: `ast.spl:1-14`, `ast_types.spl:22-33`,
  `types.spl:94-101`; `ast_reset_seq` proves indices unstable across resets.
- SIMD files exist (NEON, SVE2 721L, AVX-512, RVV 226L + 8 `encode_rvv_*.spl` incl.
  Zvk); stale doc confirmed: `doc/08_tracking/simd_implementation_status_2026-05-02_evening.md:146,295`
  claims RVV "does not exist" — **doc drift proven**, motivating the generated registry.
- GPU: `gpu_portable_compute.spl:18-20` U32/F32 only; `ptx_builder.spl:67` hardcodes
  `.version 7.8`; `cuda_backend.spl:565,572,579,586-588,610-611` — 8-byte
  offsets/loads/GEP + i64 cast default confirmed. Note `cuda_type_mapper.spl:272-295`
  already has correct per-type sizes — **the fix is wiring, not new code**.
- GPU intrinsics string-matched: `gpu_intrinsics.spl:17` (`match name:` over
  `gpu_global_id*`, `gpu_warp_*`, `gpu_atomic_*`) + second string dispatch in
  `cuda_backend.spl:616+`.

### 13.5 Net effect on the plan

All §1 audit premises held. Three refinements: (1) checked-in Lean proofs are already
sorry-free — the gap is the *generator*, not proof debt; the sorry gate needs a
non-substring matcher. (2) CUDA layout fix is mostly wiring `cuda_type_mapper` into
`cuda_backend`. (3) Lane B must build rename semantics from scratch (LSP has none) and
should hook `W-DOC-AST-001` into the existing `.md` lint walk rather than a new tool.

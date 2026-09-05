# Simple Targeted Build, Interface Compatibility, and Minimal Bootstrap Plan

**Status:** proposed architecture and parallel implementation plan
**Date:** 2026-08-10

Companion docs:
- `doc/05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md` (cache/formal design)
- `doc/03_plan/compiler/cache/semantic_incremental_build_v2_plan_2026-08-09.md` (C0–C11 cache waves)
- `doc/03_plan/compiler/perf/compiler_interpreter_performance_program_2026-08-10.md` (performance program)

---

## 1. Executive decision

Replace file-change-driven bootstrap invalidation with a **target graph plus typed dependency edges**.

Central rule:

> An ordinary dependent module is recompiled only when the new provider no longer satisfies the compile-time interface requirements recorded when that dependent was compiled.

Use four separate identities, not one vague "dependency version":

```text
ImplementationDigest    — function body / private implementation changed
CompileInterfaceDigest  — caller-visible type-checking / name-resolution assumptions changed
AbiInterfaceDigest      — already-generated machine code can no longer call/access safely
CompileSemanticDigest   — macros, compile-time constants, AOP selection, plugins, inlining
                          contracts, and compiler passes whose implementations affect artifacts
```

The normal library dependency edge uses only CompileInterfaceDigest. A compiler pass used as a tool uses CompileSemanticDigest or ImplementationDigest.

Architecture:

```text
Named build targets
    ↓ Resolver-owned typed dependency graph
    ↓ Per-module implementation and interface identities
    ↓ Per-consumer requirement manifests
    ↓ Exact/compatible/unknown/incompatible checker
    ↓ Red-green invalidation propagation
    ↓ SMF compact compatibility metadata + CAS evidence
```

---

## 2. Current Simple state

### 2.1 Bootstrap is partially incremental but still broadly invalidated

Simple defaults to dynload, reuses per-module native/SMF artifacts, and avoids full CLI relink unless requested. But `bootstrap_wide_inputs_hash()` includes every `.spl` under `src/compiler` plus broad environment/compiler context; when the aggregate hash changes, `prepare_native_cache()` removes the **entire** native cache. A body-only edit in one compiler library still causes a bootstrap-wide cache reset. **This is the primary bootstrap-minimization defect.**

### 2.2 `--target` currently means platform, not named build target

`native-build --target` takes a triple. Builds are selected through an entry file, broad source roots, and optionally an entry-import closure. There is no first-class named target like `//src/compiler:compiler`. The project manifest reader has no build-target graph.

### 2.3 Incremental invalidation is still source-oriented

The Rust bootstrap stores `semantic_exports`/`semantic_dependencies` but dirty propagation still recursively marks all reverse dependents dirty without asking whether the provider's public interface remained unchanged or compatible. Initial dependency/export discovery is line-oriented, heuristic, and hashed with Rust `DefaultHasher` — prototype quality, not an authority for safe compilation avoidance.

### 2.4 Much of the required infrastructure already exists

ApiSurface extractor; AST semantic-diff engine; canonical domain-separated action-key encoding; InterfaceDigest concept; dependency action keys (module ID + interface digest); planned CAS manifest with export and dependency-interface identities. Consolidate — do not add a parallel incremental-build system.

### 2.5 SMF has a format-audit prerequisite

Pure-Simple SMF header: fixed 128-byte trailer, 40 reserved bytes (16 already used for the compile-options hash). Inspected Rust common definition: only five reserved bytes, trailer located via `size_of::<SmfHeader>()`. These declarations appear **not wire-identical** — a P0 SMF wire-layout unification task before allocating more reserved header bytes. Compatibility metadata is therefore introduced as a **versioned SMF metadata section**, not header bytes.

---

## 3. Research conclusions

- **Tichy smart recompilation:** changes need not propagate when the declarations clients rely on are unaffected.
- **Shao & Appel smartest recompilation:** record the minimum import interface each client actually required — the foundation for per-consumer requirement manifests.
- **Rust red/green:** re-executed query with same result fingerprint keeps consumers green — a changed source may rebuild its own module, but an unchanged interface result stops dependent compilation immediately.
- **Gradle compilation avoidance:** separate implementation changes from ABI-visible changes.
- **Bazel:** targets → actions with declared inputs/outputs; action results keyed by complete inputs; immutable CAS.
- **cHash / IRHash:** hash normalized typed representations, not source lines — derive interface identity from normalized typed HIR.
- **Riker:** a correct hash over an incomplete dependency set is unsafe — be conservative about missing resolver/macro/AOP/generated/env/tool dependencies.

---

## 4. Required correctness properties

### 4.1 Compatibility result

```text
Exact        → interface identity unchanged
Compatible   → compiler proved all recorded requirements remain satisfied
Unknown      → proof unavailable; rebuild
Incompatible → recorded requirements violated
```

Only Exact and Compatible skip dependent compilation.

Guarantee: `check(requirements, provider) = PASS ⇒ provider ⊨ requirements`. A compatible change classified Unknown = wasted work (acceptable). An incompatible change classified Compatible = forbidden.

### 4.2 Scope

Soundly provable: symbol/overload compatibility; type/generic compatibility; ABI/layout; effect/capability; trait/vtable assumptions; compile-time constant and macro dependencies; default-argument compatibility under defined lowering. Not claimed: arbitrary behavioral equivalence between bodies — that's ImplementationDigest plus tool/semantic edges.

### 4.3 Bloom filters are not the authority

Bloom/XOR may skip opening a large requirement manifest when changed symbol IDs are definitely absent. Never the sole origin of a trusted compatibility lineage. Authority = typed compiler-recorded requirements + canonical interface metadata + compiler-generated compatibility certificate.

---

## 5. First-class target design

### 5.1 CLI

Positional target labels (no conflict with the platform-oriented `--target`):

```text
simple build //src/compiler:compiler
simple build //src/app/ide:ide
simple build //src/lib/std/io:smf
simple test  //test/compiler:incremental
simple query deps //src/compiler:compiler
simple query rdeps //src/compiler/parser:parser
simple build --explain //src/compiler:compiler
```

Aliases (`simple build compiler`, `simple build ide`, `simple build`) remain. Platform selection migrates toward `--platform=<triple>`; current `--target` stays as a compatibility alias during transition.

### 5.2 Target kinds

`Module, SmfLibrary, DynamicLibrary, StaticLibrary, Binary, Test, Generated, BootstrapStage, Aggregate`

```simple
struct Target:
    stable_id
    kind
    entry_points
    source_roots
    declared_inputs
    inferred_module_closure
    output_artifacts
    target_platform
    runtime_family
    enabled_features
    build_profile
```

Source imports remain resolver-inferred; a target defines the build boundary and outputs.

### 5.3 Target metadata

Simple-native `build.sdn` long-term:

```sdn
target compiler:
    kind: binary
    entry: src/app/cli/main.spl
    source_roots:
        src/compiler
        src/app
        src/lib
    default: true
    output: bin/simple

target compiler_tests:
    kind: test
    roots:
        test/01_unit/compiler
    depends:
        compiler
```

Migration: (1) infer a default target from current entry/source-root options; (2) add a `build.sdn` reader; (3) keep a compatibility adapter for `simple.toml` and CLI builds; (4) make `build.sdn` authoritative, legacy flags become synthetic targets. Target visibility follows existing MDSOC folder/publicization rules.

---

## 6. Typed dependency graph

| Edge | Invalidated by | Required action |
|---|---|---|
| CompileInterface | Unsatisfied source interface requirement | Recompile consumer |
| Abi | ABI/layout incompatibility | Recompile or reject old object |
| Link | Provider implementation artifact changed | Relink final image |
| Runtime | Loaded implementation changed | Reload/rebind |
| CompileSemantic | Macro/const-eval/inline/AOP semantic root changed | Recompile semantic consumers |
| Tool | Compiler/code generator implementation changed | Re-run producing action |
| Generated | Generated source/data changed | Rebuild consumers |
| Resolution | Module-selection witness changed | Resolve and possibly recompile |
| AopSelection | Pointcut or applicable advice set changed | Reweave target |

(The existing AOP cache design already separates advice body / advice interface / selection / link plan — same principle.)

---

## 7. Canonical interface signatures

### 7.1 Extract from typed HIR

Authoritative extractor runs after parse → name resolution → type resolution → generic/effect analysis, before ordinary bodies become part of interface identity. Never derive from source lines or formatted AST text.

### 7.2 Roots

```simple
struct ModuleIdentity:
    source_digest
    implementation_digest
    compile_interface_digest
    abi_interface_digest
    compile_semantic_digest
    link_export_digest
```

**Compile interface includes:** stable public symbol IDs; visibility; namespace/overload-set membership; parameter types and passing modes; parameter names only when named args/reflection make them semantic; return type; generic arity + constraints; effects/capabilities; ownership/borrowing contract; trait/interface requirements; public enum variants + exhaustiveness semantics; public constants visible to type checking or CTFE; public methods and associated types.

**ABI interface additionally:** calling convention; mangled symbol identity; type representation; field offsets/sizes/alignment/packing where exposed; enum representation + discriminants; vtable/interface slot ordering; exception/unwind ABI; ownership transfer + return-value convention.

**Compile-semantic interface:** exported macros; compile-time functions; substituted constants; inline-always bodies; derive/codegen rules; AOP pointcut selection + advice interface; target configuration altering generated code.

### 7.3 Canonical encoding

Same as the action-key layer: domain separation, length-prefixing, schema versioning, stable symbol IDs, sorted unordered collections, explicit ordering where semantic, SHA-256. Paths, comments, formatting, line numbers, private declarations, ordinary bodies never enter CompileInterfaceDigest. Recursive types/import cycles: SCC-based canonicalization.

---

## 8. Consumer requirement manifests

A whole-module interface hash is the first fast path but too coarse. Each compiled consumer emits the exact requirements it used (`.sreq`):

```text
consumer: compiler.type_checker
provider: compiler.parser

requirements:
    symbol parser.Parser.parse:
        parameter_types: [TokenStream]
        return_type: Ast
        effects: pure
        calling_convention: simple

    type parser.Token:
        fields_used: { kind: TokenKind, span: SourceSpan }

    enum parser.TokenKind:
        exhaustive_match: false

    overload parser.parse:
        selected_symbol: parser.Parser.parse(TokenStream)
        candidate_set_digest: ...
```

Generated by the resolver/type checker while actual calls, fields, layouts, constants, traits, and exhaustive matches are resolved. Permits: changing an unused export without rebuilding a consumer; removing an export a consumer never used; adding methods without invalidating field-only consumers; adding enum variants without invalidating non-exhaustive consumers; no global rebuilds for unrelated overload sets.

---

## 9. Compatibility policy

### 9.1 Transitions

| Change | Compile compat | ABI compat | Action |
|---|---|---|---|
| Function body only | Exact | Exact | Rebuild provider; relink/rebind only |
| Private declaration added/removed | Exact | Exact | Provider only |
| Distinct public function name added | Compatible | Compatible | No consumer compile |
| New overload under existing name | Consumer-specific | Usually compatible for old binary | Check recorded overload resolution |
| Public function removed | Consumer-specific | Incompatible for users | Check `.sreq`; rebuild/error users |
| Parameter type changed | Incompatible | Incompatible | Recompile users |
| Return type changed | Incompatible | Usually incompatible | Recompile users |
| Generic bound relaxed | Usually compatible | Usually unchanged | Prove structurally |
| Generic bound tightened | Incompatible for some | Possibly unchanged | Recompile affected users |
| Effect weakened | Compatible candidate | Usually unchanged | Prove effect subtyping |
| Effect strengthened | Incompatible | May remain same | Recompile affected users |
| Public struct field added | Source-dependent | Often ABI-breaking | Separate compile and ABI decisions |
| Field reordered/type changed | Incompatible | Incompatible | Recompile |
| Enum variant added | Consumer-specific | Representation-dependent | Rebuild exhaustive-match consumers |
| Trait method added with default | Often compatible | Vtable-dependent | Check implementer + ABI requirements |
| Required trait method added | Incompatible | Potentially incompatible | Recompile implementers |
| Macro/const-eval result changed | Ordinary interface may be exact | N/A | Recompile semantic consumers |
| AOP advice body changed | Compile interface exact | Link/runtime changed | Relink/rebind |
| AOP pointcut/signature changed | Semantic/interface changed | Possibly changed | Reweave affected targets |

### 9.2 Adding default-valued parameters

`fn read(path)` → `fn read(path, cached = Default)` must not automatically be compatible if the old symbol disappears. The compiler preserves the old entry point as a compatibility thunk:

```simple
fn read(path: Path) -> Data:
    read(path, CacheMode.Default)
```

Old ABI symbol remains valid; the checker proves preservation; the default is applied by the thunk, so a changed default expression does not recompile every old caller.

### 9.3 Added overloads

A new overload under an existing name can change resolution even without removals. Compatible for a consumer only when its recorded resolution witness proves the selected old call is unchanged; otherwise Unknown → recompile that consumer.

---

## 10. Fast interface-version check

### 10.1 Version numbers are summaries, not authority

Manual `api_version: 7` is release communication only. The compiler issues a lineage after running the checker:

```simple
struct InterfaceVersion:
    exact_interface_digest
    compatibility_lineage_digest
    generation
    compatible_from
```

Breaking transition = new lineage. Compatible transition = advance generation.

### 10.2 Hot-path check

```text
if consumer.exact == provider.exact: Exact
elif consumer.lineage == provider.lineage
     and provider.compatible_from <= consumer.required_generation <= provider.generation:
    Compatible
else:
    check consumer requirement manifest
```

One 32-byte digest compare in the dominant case; lineage + two integer compares for additive changes; no AST/HIR parsing, no structural comparison on the hot path. A daemon may intern verified digests into compact integer IDs.

### 10.3 Branching compatibility

`compatible_from..generation` handles linear evolution. Non-contiguous compatibility uses a new lineage or explicit predecessor certificates in the CAS — never force incompatible branches into one range.

---

## 11. Invalidation algorithm

```text
build(requested targets):
    resolve target closure; load previous action/interface metadata

    for each changed source:
        rebuild its own module action
        compute new implementation/interface/ABI/semantic roots

        if compile_interface_root unchanged:
            do not dirty ordinary compile dependents
        else:
            for each compile consumer:
                if provider satisfies recorded consumer requirements: keep green
                else: recompile consumer

        if ABI root changed:       invalidate affected object/link/runtime edges
        if semantic root changed:  invalidate only recorded semantic consumers
        if impl artifact changed:  relink or rebind including targets

        after recompiling a consumer:
            compare new interface root with old; stop propagation when unchanged
```

**Compiler-component distinction:** an optimizer library changing internally with the same callable interface yields two relationships — `compiler_driver --CompileInterface--> optimizer` (driver need not recompile) and `generated_object --Tool--> optimizer implementation` (artifacts produced by the changed optimizer may need regeneration).

---

## 12. Minimal bootstrap design

### 12.1 Bootstrap becomes a target graph

```text
//bootstrap:seed  //bootstrap:stage1-compiler  //bootstrap:stage2-compiler
//bootstrap:stage3-compiler  //bootstrap:stage4-cli  //bootstrap:convergence
//bootstrap:deploy  //bootstrap:release-proof

//src/compiler/frontend:parser  //src/compiler/frontend:resolver
//src/compiler/semantic:type_checker  //src/compiler/mir:optimizer
//src/compiler/backend:llvm  //src/compiler/driver:driver  //src/app/cli:simple
```

```text
simple bootstrap //src/compiler/frontend:parser
simple bootstrap //bootstrap:stage3-compiler
simple bootstrap //bootstrap:convergence
```

### 12.2 Replace the bootstrap-wide cache stamp

Remove `any src/compiler source changed → clear entire native cache`. Replace with:

```simple
struct BootstrapContextDigest:
    platform; backend; runtime_family
    compiler_schema; resolver_schema
    aop_matcher_weaver_schema; loader_abi_schema; target_graph_schema
```

Each module action carries source digest, tool/component semantic digests, dependency interface requirements, target configuration, macro/AOP roots, resolution witnesses. Ordinary edits cause action misses only in affected nodes. Even `--fresh-cache` distinguishes "clear action/index aliases" from "delete immutable CAS blobs" (the latter for corruption recovery/explicit cleanup only).

### 12.3 Bootstrap behavior by change type

- **Library implementation-only:** rebuild changed SMF/object; no caller compile; relink static image or rebind dynload module; no cache clear.
- **Parser implementation:** rebuild parser; invalidate parse actions from old parser semantic identity; reparse target closure; compare normalized AST results; keep later phases green where unchanged.
- **Type checker implementation:** invalidate type-analysis actions; compare typed HIR/interface results; avoid MIR/codegen where unchanged.
- **Codegen implementation:** invalidate generated object actions; retain parse/HIR/MIR inputs; relink only requested targets.
- **Loader ABI / SMF schema:** broad incompatibility; rebuild affected loadables; possibly full convergence/release proof.

### 12.4 Development and release gates

Default developer path is minimal (`simple build <target>` / `simple test <focused>`); a changed compiler component does not force full bootstrap merely for residing under `src/compiler`. But: deploying a new trusted compiler runs staged convergence; release retains a clean full bootstrap + deterministic comparison gate; strict CI periodically shadows interface-aware results against a clean build. Minimization speeds ordinary work; it does not remove the release proof.

---

## 13. SMF and related metadata design

### 13.1 P0: unify the wire schema

Authoritative schema, e.g. `src/spec/artifact/smf_v1_2.sdn`, generating/validating Pure-Simple and Rust-seed `SmfHeader`, reader/writer offsets, header/trailer size, section entry size, endianness, alignment. Required tests: sizeof/field-offset parity; Rust writes → Simple reads and vice versa; v1.0 header read; v1.1 trailer read; unknown-section behavior; truncated/corrupt rejection. No new fixed-header field before this gate passes.

### 13.2 Generic metadata section `.simple_meta`

Versioned TLV records:

```simple
struct MetaRecordHeader:
    kind: u16; version: u8; flags: u8; payload_length: u32
```

Kinds: `CompileOptions, InterfaceCompatibility, AbiCompatibility, DependencyRequirements, ActionManifestReference, AopIdentity, BuildProvenance`.

### 13.3 Strict compact interface record

```text
InterfaceCompatibilityV1:
    exact_compile_interface_sha256: [32]  # 32 B
    compatibility_lineage_sha256:   [32]  # 32 B
    generation:                     u32   #  4 B
    compatible_from:                u32   #  4 B
                                          = 72 B (+8 TLV = 80 B/module)
```

Full 256-bit digests — a truncated hash must not become the trusted boundary. Dynamic/native ABI modules add optional `AbiCompatibilityV1` (exact_abi_sha256, abi_schema, flags) = +48 B incl. TLV. Ordinary SMF ≈ 80 B; dynload/public-ABI ≈ 128 B, fixed-size regardless of export count.

### 13.4 Dependency requirements

Do not embed a full symbol/interface tree per SMF. SMF holds interface quick metadata + compact direct-edge table + CAS reference to detailed `.sif`/`.sreq`. Edge format: module-table varint index, edge kind u8, lineage-table varint index, required generation varint, flags u8, optional requirement-manifest index. Budgets: typical edge 4–12 B; 100 direct deps ≈ 0.4–1.2 KB; full symbol requirements external. Bloom/XOR prefilter only above a requirement-count threshold, always with an exact backing manifest.

### 13.5 Compile-options migration

Continue reading the v1.1 reserved-byte representation; dual-write old + `CompileOptions` TLV during transition; prefer the TLV; stop writing reserved bytes only after all supported readers consume the new metadata; conflicting duplicate metadata = corruption, not a hit.

### 13.6 LSMF archive changes

Next `.lsm` version: retain offset/size for fast lookup; add SHA-256 artifact identity or reference into an archive digest table; keep FNV only as an optional quick corruption checksum; do not duplicate interface metadata in the index; read each embedded SMF's `.simple_meta`; archive identity = sorted module name → artifact digest mappings.

### 13.7 Non-SMF artifacts

Same schema for native objects, static/dynamic libs, executables, cached HIR/MIR, generated source. Where embedding is unavailable: `artifact.ext` + `artifact.ext.smeta`. One logical `SimpleArtifactMetadata` API regardless of physical format.

---

## 14. Formal verification plan

Extend the existing Lean cache-identity work with an interface-compatibility model. Core: `Declaration, Interface, ConsumerRequirement, CompatibilityRule, CheckResult, Satisfies`.

Required theorems:

```text
exact_pass_sound              # exact_digest_equal → satisfies
compat_pass_sound             # checker = Compatible → satisfies
added_unreferenced_symbol_sound
preserved_symbol_signature_sound
default_parameter_thunk_sound
requirement_subset_sound
unknown_never_reused
encoding_injective_for_canonical_interfaces
ordering_independent_for_interface_sets
```

Anything not covered by a proved rule returns Unknown. Implementation mirrors the Lean model the way `action_key.spl` mirrors the cache-identity model.

---

## 15. Diagnostics and observability

```text
simple build --explain <target>
simple interface show <module>
simple interface diff <old> <new>
simple interface check <consumer> <provider>
simple cache explain <module>
simple query why-rebuilt <module>
```

Example explain output:

```text
compiler.type_checker: REUSED
provider: compiler.parser
source: changed
implementation: changed  90ab...
compile interface: unchanged  11cd...
ABI: unchanged  4e72...
decision: dependent compilation skipped
link action: parser.smf changed; compiler image rebound
```

Compatible additive change:

```text
compile interface: changed
compatibility: compatible
rule: AddedDistinctPublicFunction
lineage: 472d...   generation: 18 -> 19
consumer requirement: satisfied
decision: no dependent compilation
```

---

## 16. Parallel-agent implementation plan

| Agent | Ownership | Main outputs | Depends |
|---|---|---|---|
| A0 Integration owner | Architecture contracts, merge sequence, shared schemas | Approved schemas, feature flags, integration decisions | all |
| A1 SMF format audit | Existing Simple/Rust readers, writers, layouts | Wire-layout report, cross-language fixtures, generated schema plan | — |
| A2 Target graph | Named targets, labels, graph query, manifest adapter | Target IR, CLI query mode, `build.sdn` reader | A0 |
| A3 Interface extractor | Typed-HIR public interface and roots | Canonical signature IR, compile/ABI/semantic digests | A0 |
| A4 Requirements + compatibility | `.sreq`, checker, lineage, certificates, Lean | Sound compatibility engine and proofs | A3 |
| A5 Incremental scheduler | Typed edges, red-green propagation, action planning | Minimal rebuild planner, explain traces | A2, A3 |
| A6 SMF/LSMF metadata | `.simple_meta`, dual readers/writers, archive update | SMF v1.2 metadata implementation | A1, A3, A4 |
| A7 Bootstrap integration | Stage targets, cache policy, wrapper migration | Minimal bootstrap path, removal of broad clear | A2, A5 |
| A8 Verification + performance | SSpec/system tests, shadow builds, benchmarks | Correctness matrix, rebuild-count dashboards | consumes all |

File ownership boundaries:

```text
A2: src/compiler/80.driver/build_graph/, build.sdn parser, target-query CLI modules
A3: src/compiler/30.semantic/interface/, canonical interface encoder
A4: src/compiler/80.driver/cache/interface_compat.spl, .../requirements.spl,
    src/verification/interface_compat/
A5: incremental graph/scheduler modules, legacy incremental adapter
A6: smf_header/writer/readers, lib_smf format, Rust mirror readers/writers
A7: scripts/bootstrap/, bootstrap target declarations, bootstrap architecture docs
A8: test/, scripts/check/, benchmark and generated evidence
```

Only A6 edits shared SMF wire structures. Only A7 edits the bootstrap wrapper. Cross-cutting CompileOptions/CLI dispatch changes merge via A0 after owning agents expose stable APIs.

---

## 17. Execution waves

**Wave 0 — Contracts and baseline (parallel).** A1: format audit — enumerate every SMF/LSMF reader/writer, determine actual wire sizes/offsets, produce Rust↔Simple round-trip fixtures, identify legacy files. A8: baseline — measure cold full bootstrap, warm unchanged, single compiler-body edit, private-signature edit, public additive fn, public breaking signature, macro change, AOP advice-body change, AOP pointcut change, codegen implementation change; record modules parsed/typed/lowered, objects/SMFs generated, links, cache bytes deleted, wall/CPU, peak memory. A0: freeze target-label grammar, typed edge enum, InterfaceSignatureV1, ConsumerRequirementV1, SimpleArtifactMetadataV1, compatibility-result semantics. *Exit:* no agent invents its own hash fields or compatibility meaning.

**Wave 1 — Compute-only infrastructure (A2, A3, A6 prototype).** A2: labels + graph IR; synthesize legacy target from current flags; `simple query targets/deps/rdeps`; no build-selection change yet. A3: canonical interface roots from typed HIR; compare vs ApiSurface; compile/ABI/semantic roots; log-only. A6: generic metadata record parser/writer + fixtures; not cache-controlling yet. *Exit gates:* body/comment/private changes → same CompileInterfaceDigest; public signature change → different; declaration-map iteration order → identical digest; target closure matches resolver-owned entry closure.

**Wave 2 — Compatibility and red-green planning (A4, A5).** A4: Exact, AddedDistinctSymbol, PreservedOldSymbol, DefaultParameterThunk, EffectWeakening, RequirementSubset, Unknown, Incompatible; `.sreq` from actual type-resolution events. A5: typed edges + optimized rebuild plan, old behavior authoritative, new plan logs what it would reuse; compare rebuild sets. *Exit:* every new-plan reuse decision has an exact digest match or a compatibility certificate.

**Wave 3 — SMF dual metadata and shadow reuse.** A6: emit `.simple_meta`; dual-read old/new compile-options; interface + requirement references; update all readers + `.lsm`; missing metadata = Unknown. A5: shadow reuse — optimized vs clean reference outputs, normalize known-nondeterministic sections, compare artifact + interface roots. A8: mutation-driven tests for every rule and every Unknown fallback. *Exit:* zero stale reuse across the mutation matrix.

**Wave 4 — Target build activation.** A2: positional targets authoritative; legacy flags become synthetic targets. A5: execute only the requested closure. A8: assert unrelated target trees are not parsed/typed/compiled. *Exit:* selected-target builds no longer load broad workspace roots outside the proven closure.

**Wave 5 — Bootstrap migration.** A7: replace `bootstrap_wide_inputs_hash → rm -rf native_cache` with target/action metadata; introduce `simple bootstrap //bootstrap:stage3-compiler|convergence|release-proof`; Tool edges between stages + red-green phase output comparisons; keep legacy behind `--bootstrap-invalidation=legacy` during shadow validation. *Exit gates:* body-only compiler edit → no global clear, no dependent compile, provider rebuild + link/rebind only; public additive → no dependent compile; breaking signature → only requirement-affected reverse closure; codegen change → frontend artifacts reused, affected objects regenerated; release proof: clean bootstrap available and passing.

**Wave 6 — Default transition.** Enable target graph, exact-interface avoidance, proved additive compatibility, minimal bootstrap by default; retain strict clean mode for CI/release; remove heuristic line-based semantic exports after resolver-owned capture has full coverage; retire the broad cache stamp; keep legacy SMF readers for one documented compatibility window.

---

## 18. Verification matrix

**Interface:** comments-only; formatting-only; private body; private declaration; public body; public distinct fn addition; overload addition; fn removal; parameter/return type change; effect weaken/strengthen; generic-bound relax/tighten; struct field add/reorder/type change; enum variant addition (exhaustive and non-exhaustive consumers); trait default/required method addition; default parameter with/without thunk.

**Semantic edges:** macro implementation; macro contract; compile-time constant; const evaluator; inline-always body; AOP advice body; AOP pointcut; AOP priority/order; parser; type checker; optimizer; code generator; module resolver; loader.

**Targets:** single; aggregate; two independent; generated dependency; cyclic module SCC; cross-runtime-family; platform-specific; MDSOC visibility violation; AOP target selection.

**Format:** v1.0/v1.1/v1.2 SMF; unknown metadata record; missing metadata; duplicate conflicting record; truncated metadata; incorrect digest; Rust-written/Simple-read and inverse; LSMF round trip.

**Bootstrap:** no-change warm; frontend body-only; backend body-only; interface-compatible addition; breaking interface; runtime ABI change; SMF schema change; stage resume; dynload; one-binary; clean release.

---

## 19. Acceptance criteria

**Correctness.** Every skipped compilation justified by exact equality or a validated compatibility proof; Unknown always rebuilds; missing/legacy metadata never enters trusted global cache as compatible; Bloom/XOR never creates a lineage; clean and incremental builds produce identical deterministic outputs (or identical normalized semantic outputs); formal proofs contain no unproved placeholders.

**Rebuild precision.**

| Scenario | Required result |
|---|---|
| Body-only library edit | Provider compile only; dependent count zero |
| Private declaration edit | Provider only |
| Distinct public fn added | Dependent count zero |
| Added overload | Only resolution-affected/unknown consumers compile |
| Removed unused export | Non-requiring consumers stay green |
| Breaking signature | Requirement-affected reverse closure only |
| Advice body only | No reweave; relink/rebind |
| Pointcut/signature change | Affected targets reweave |
| Compiler implementation change | Produced actions invalidate; callers don't rebuild for API |
| Unrelated named target | No parse/type/codegen work |

**Bootstrap.** Ordinary compiler body edits do not delete the native cache; target-only builds don't compile the full CLI outside the closure; full CLI relink only for static final images, deployment, one-binary, release proof; release retains clean bootstrap/convergence.

**Metadata/performance.** Ordinary SMF interface metadata ≤ ~80 B; dynload/public-ABI ≤ ~128 B; detailed interfaces/requirements in CAS; exact hot path needs no parsing or sidecar read after admission; typical edge metadata < ~12 B via interning + varints; no whole-cache deletion for an individual edit.

---

## 20. Recommended first implementation slice

1. Fix and test the SMF Rust/Simple wire-layout contract.
2. Generate CompileInterfaceDigest from typed HIR.
3. Store the digest in a new `.simple_meta` section.
4. Record only whole-module exact interface requirements initially.
5. Change dirty propagation: rebuilt provider with unchanged interface root does not dirty compile dependents.
6. Run in shadow mode against full rebuilds.
7. Replace the bootstrap-wide cache clear only after zero shadow divergence.
8. Add per-symbol `.sreq` and additive compatibility rules afterward.

The first slice delivers the largest low-risk gain — `body change → rebuild provider → compare interface root → stop propagation` — building on existing action-key, CAS, semantic-export, and SMF metadata work. The finer "smartest recompilation" layer (consumer-specific requirements, additive compatibility, lineage versions, default-parameter thunks) adds later without changing the core target/action architecture.

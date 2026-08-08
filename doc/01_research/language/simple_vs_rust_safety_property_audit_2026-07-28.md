# Simple vs Rust — Safety-Property Parity Audit

**Date:** 2026-07-28
**Profile naming (2026-07-28):** Profile ladder renamed: moderate, strict (formerly lib), robust (formerly reliable), critical (formerly mission-critical). This document's audit scope is the `robust` and `critical` profiles; see `doc/02_requirements/language/mission_critical_profile.md`.
**Parent plan:** `doc/01_research/language/simple_vs_rust_mission_critical_2026-07-27.md`
**Purpose:** property-by-property audit of Rust-class memory/concurrency safety in Simple
robust mode. The question is not whether Simple has these concepts, but whether each is
**enforced by the production self-hosted compiler on every relevant path** — vs existing
only as designs, Lean models, runtime checks, or Rust-seed-only implementations.
**Scope exclusion (design decision, not a gap):** Simple's deliberately short borrowing
range — Simple allows borrows but restricts their range; this is accepted design, not a
deficiency to "fix" toward Rust.

**Status vocabulary:** `implemented-enforced` | `partial` | `modeled-only` (Lean/formal
only) | `proposed` (design doc only) | `missing` | `conflicts-with-design`.

## Required robust-mode properties

1. **Use-after-free prevention** — after move, destroy, pool release, scope exit, or
   owner invalidation, all dependent references and iterators statically unusable.
   Generation checks are defense-in-depth, not the primary guarantee.
2. **Dangling-reference prevention** — no ref-to-local returns, no storing refs past
   owner lifetime, no stack refs in longer-lived closures, no borrows across suspension
   unless proven suspension-safe, no refs surviving container reallocation. Needs an
   internal lifetime graph; syntax can stay inferred/simpler than Rust.
3. **Aliasing control** — Shared (many, no ordinary mutation) / Exclusive (one, mutates)
   / Isolated (no aliases, transferable) / interior-mutable (container protocol) / raw
   (explicit unsafe boundary). Robust mode must reject, not warn.
4. **Data-race prevention** — share-nothing + copy-on-send default; structural
   Send/Sync-equivalents (Transfer, Share, CoreLocal, InterruptSafe, DmaSafe,
   AtomicSafe) derived from fields/generics, never unchecked annotations.
5. **Iterator-invalidation prevention** — default iterators borrow the collection
   (mutation while iterating = compile error); explicit generation-checked
   `CheckedCursor<T>` (returns `Invalidated`) as the opt-in mutation-tolerant form.
6. **Object-lifetime enforcement** — every object has one lifetime policy
   (stack/scope/moved/arena/pool/refcounted/static/borrowed/device-owned); ambiguous
   lifetime class rejected; arena values cannot escape their arena; no silent
   actor/task-handle orphaning by default.
7. **Double-release prevention** — affine/move-only handles (`close(move handle)`
   consumes; second close = compile error); pool release consumes; generation counters
   guard serialized/cross-task IDs only.
8. **Checked pointer arithmetic** — safe ops (`slice[i]`, `subspan`, `offset_checked`)
   carry bounds/overflow/scaling/alignment/provenance; raw offset only inside explicit
   unsafe boundary with justification; pointers keep allocation identity, base, extent,
   element type, alignment, address space, mutability, lifetime, provenance. MMIO/DMA
   via dedicated types (`MmioRef<Reg>`, `DmaBuffer<OwnedByDevice>`, `ForeignPtr<T>`),
   never plain integers.
9. **Controlled interior mutability** — shared ref prohibits ordinary unsynchronized
   mutation; mutation only via explicit-protocol containers: `Cell`, `RefCell`,
   `Mutex`, `RwLock`, `Atomic`, `ActorCell`, `InterruptCell`; restrictions structural
   (RefCell not cross-thread; Mutex shareable only if T transferable; interrupt-safe
   containers can't block; actor-local can't escape actor).
10. **Synchronization safety** — unlock exactly once; no guard-after-unlock; lock-order
    levels (`@lock_level(n)`, acquiring lower after higher fails without reviewed
    exception); no blocking lock in interrupt context; no suspension holding a
    non-`SuspendSafe` lock (`await` under `lock()` = error); atomic-ordering validity;
    condvar/channel close-drain protocols; deadlock/priority-inversion policy.
11. **Cancellation and suspension safety** — every suspending op declares one of
    `CancelSafe | CancelAtomic | CancelRollback | CancelConsumes | NonCancellable`; no
    hidden cancellation points; no cancellation while invariants broken; defer/cleanup
    runs on cancel; structured scopes cancel+drain children before propagation;
    partial I/O returned explicitly; persistent updates in cancel-safe transactions.

## Target comparison (assuming full enforcement)

| Property | Rust | Simple robust-mode target | Critical (mission-critical) profile |
|---|---|---|---|
| Use-after-free | ownership/borrow | same + optional generation handles | same, with generation handles mandatory |
| Dangling refs | lifetimes | same, mostly inferred | same, inferred + proved |
| Aliasing | `&`/`&mut` | shared/exclusive/isolated capabilities | same, with proof coverage |
| Data races | ownership + Send/Sync | share-nothing default + structural share capabilities | same, with proof coverage |
| Iterator invalidation | borrow-based | borrow-based + explicit generation cursors | same + generation mandatory |
| Object lifetime | RAII/Drop | deterministic scope/arena/pool policies | same + proof/manifest |
| Double release | move + RAII | affine ownership + generation validation | generation mandatory + proof |
| Pointer arithmetic | unsafe raw | checked provenance ptrs; raw confined to reviewed boundaries | same + capability-scoped @unsafe(reason, capabilities:[...]) |
| Interior mutability | UnsafeCell family | explicit protocol containers | same + RAII guards only |
| Cancellation | library/runtime | language-level cancellation-effect contracts | same + effects manifest |
| Suspension safety | pinning + borrows | borrow + suspension-effect checking | same + proof |
| Domain primitives | allowed | prohibited at robust boundaries | prohibited everywhere in code + proof |
| Proof coverage | external | integrated, gateable | no sorry/admit/axioms, manifest-reviewed only |
| Semantic doc links | limited | required stable symbol links | required stable symbol links (fail-closed) |

## Claimed repository status (pre-verification, from assessment)

- Capability model Shared/Exclusive/Isolated documented + formally modeled; concrete
  checker reportedly a **Rust-side implementation**, self-hosted path unconfirmed.
- Concurrency semantics doc **proposed**, not accepted-implemented; cross-task
  mutable-sharing diagnostics **explicitly not implemented**; no-GC enforcement relies
  partly on runtime copying.
- Formal memory model (happens-before, locks, atomics, SC-DRF) exists as model — does
  not by itself prove the self-hosted compiler constructs/enforces that environment.
- Iterator invalidation: no clear universal language-level enforcement evidence.
- Cancellation: cooperative, suspension-point-only, channel-atomic intended, stream I/O
  possibly not cancel-safe, structured-scope sibling cleanup — all in a PROPOSED doc.
- Generation-handle patterns used in NVMe/resource designs — subsystem pattern, not
  proven universal language enforcement.
- No-GC actors may refcount; orphaned handles can leak **by documented design**.

**Corrected conclusion:** the remaining weakness is implementation/enforcement
completeness on the production self-hosted path, not a conceptual deficiency vs Rust.

## Verification matrix (agent-verified repo ground truth, 2026-07-28)

Four-agent sweep complete. Verdict column is for the **production self-hosted path**
(`src/compiler/**/*.spl`) unless noted.

| # | Property | Verdict | Key evidence |
|---|----------|---------|--------------|
| 1 | Use-after-free / use-after-move | **missing in practice (dead code)** | `borrow_graph.spl:364,452-461` diagnostic exists BUT `moved_places` is keyed per program-point and read only at the same point (a move at pt 3 + use at pt 7 is undetectable by construction); `MirInstKind.Move` built only by `emit_move` (`mir_data.spl:337-343`) which has **zero callers**; borrow "tests" `borrow_check_move_{1,2,3}_spec.spl` are `check(1+1==2)` filler, the one real assertion commented out (`borrow_check_spec.spl:246`) |
| 2 | Dangling references | **partial / proposed** | outlives machinery real (`lifetime.spl:431-453`, `nll.spl:336-345`) but constraints generated ONLY from explicit unary `&`/`&mut` (`expr_dispatch.spl:2241-2243`); return-ref-to-local NOT rejected — escape analysis is an optimization hint, emits no error (`gc_analysis/escape.spl:181,229`); borrow-across-await: zero hits in `55.borrow/**` |
| 3 | Aliasing control | **partial, near-vacuous** | full 1776-line NLL checker (`55.borrow/borrow_check/`) wired on-by-default (`driver_pipeline.spl:223-243`, `no_borrow_check:false`) detecting E0502/assignment-while-borrowed — but ordinary code emits almost no `Ref` instructions, and `--no-borrow-check` bypasses it; `iso`/Isolated parsed (`parser_types_expr.spl:33`) but **no .spl checking pass** — name-mangling metadata only (`monomorphize/util.spl:221-228`); Lean model complete (`MemoryCapabilities.lean:12-103`); Rust seed checks ONLY actor-mode compat (`function.rs:571-572`), has **no borrow checker** |
| 4 | Data races | **proposed / modeled-only** | doc itself says diagnostic "not yet implemented" (`concurrency_semantics.md:264-273`, header = PROPOSED); copy-on-send is prose only — no implementation in `nogc_async_mut/`; **no Send/Sync analogue** (Transfer/Share) anywhere; SC-DRF Lean model exists (`MemoryModelDRF.lean`) with no linkage to compiler atomics |
| 5 | Iterator invalidation | **missing** | stdlib `Iterator<T>` is a closure pair (`iterator/create.spl:3-9`) — no cursor, no generation, nothing to invalidate against; zero guards, zero tests; the compiler itself manually dodges it (`generation_sweeper.spl:76` "cannot modify dict during iteration") |
| 6 | Object lifetime policies | **partial (library, ad-hoc)** | reusable `HandleArena<T>` with generations exists (`engine/resource/handle.spl:1-30`) but adoption ad-hoc: storage arena + object_pool each have independent schemes; **NVMe arena hardcodes generation≡0** (`raw_nvme_arena.spl:160,178`) so those handles are NOT generation-protected; ~4 divergent copies across tier families; actor orphan-handle leak is **by documented design** (`concurrency_semantics.md:466-468`) |
| 7 | Double release | **missing (compiler) / partial (runtime)** | no affine/consuming-API enforcement; `@must_use` is an interpreter registry (`eval_tables.spl:286-319`); detection is sanitizer-runtime only (asan/msan) |
| 8 | Pointer arithmetic + bounds | **mixed** | slice indexing IS enforced: tree-walk interp (`eval_access.spl:105+`) + LLVM native trap (`runtime.c:1817-1823`) — BUT three holes: **MIR interpreter silently ignores OOB** (`mir_interpreter.spl:634-643` returns 1, no abort); lowering silently bails when base type has no len symbol (`expr_dispatch.spl:856-861`); no trap in freestanding/baremetal C. Raw pointers are integer addresses with zero provenance (`ptr/raw.spl:8-17`); `PtrState` valid/moved/expired is cooperative library bookkeeping only |
| 9 | Interior mutability | **partial** | Atomics REAL (`std::sync::atomic`-backed, correct orderings, `atomic.rs:962-999`); Mutex/RwLock exist but protocol unenforced — manual unlock, **no guard/RAII** (`mutex.spl:20-42` "no automatic unlock"); async-tier mutex is an **empty stub**; Cell/RefCell **do not exist** (only variance test fixtures); no cross-thread-shareability restriction |
| 10 | Plain-shared-ref mutation | **legal and deliberate** | `fn f(state: DeviceState): state.status = X` mutates the caller's object BY DESIGN — `function_lowering.spl:250-256` routes mutation through ANY class param (fix for s19 mutation-dropped bug); `me` metadata never consumed by a checker; `E1047 CANNOT_BORROW_MUT_FIELD` declared (`error_codes.spl:56`) but **never emitted**; `mutability_control.md` = Status: Planned |
| 11 | Synchronization safety | **runtime-only** | lock-order = TSan runtime deadlock detection (`tsan/mod.spl:138-168`); no compile-time guard-after-unlock / suspend-while-locked / `@lock_level` checks; `SuspendSafe`: 0 hits |
| 12 | Cancellation / suspension | **proposed + partial runtime** | `CancellationToken` implemented (`async/cancellation.spl:3-90`); spec is PROPOSED (`concurrency_semantics.md:110-176`); **no cancel-safety annotations** in src (0 hits); channel cancel-atomicity claimed in doc, **absent in code** |
| 13 | Unsafe boundary | **partial (syntax without teeth)** | `danger:`/`unsafe:` parsed by Rust parser only (`core.rs:829-836`); self-hosted `KwUnsafe` declared, never produced; `safety_checker.spl` enforces exactly ONE rule (asm-outside-unsafe), warn-only, opt-in `SIMPLE_SAFETY_WARN=1`, and has a filed bug "pass never invoked"; `RawPointerOutsideUnsafe`/`UnsafeFfiOutsideUnsafe` declared, **never constructed** |
| 14 | FFI boundary | **missing** | `pub extern fn` with raw i64 addresses directly exported to Simple code (`ptr/raw.spl:8-17,37-42`); no unsafe requirement, no wrapper generation, no marshalling validation; extern spec treats it as ordinary |
| 15 | MMIO/DMA typing | **partial (DMA > MMIO)** | DMA is genuinely typed: `DmaBuffer`/`SharedDmaBuffer` with owner, `allocation_id` release validation (`io/dma.spl:74,401`); MMIO is a typed capsule over i64 (`hal/types.spl:20-26`) with untyped read/write payloads; riscv `mmio_map` is an address-constant table, not a capability |

### Documented design conflicts (docs allow what the audit prohibits)

1. `doc/05_design/compiler/rust_migration/rust_to_simple_error_mapping.md:64,329,751` —
   claims "Simple has no unsafe" while `unsafe:`/`danger:` blocks are parsed and baremetal
   design proposes them. Docs internally contradictory.
2. `doc/02_requirements/language/di/capability_system.md:222-238` — "Unsafe = ALL
   capabilities allowed" blanket escape hatch, recorded as a *passing* requirement.
3. `doc/02_requirements/language/effects/effect_system.md:134-146` — `@unsafe` allows
   unchecked ops with no reviewed-boundary obligation.
4. `doc/05_design/hardware/baremetal_features_examples.md:135-140,945` — integer-address
   MMIO is the sanctioned design; unsafe-region borrow-check skipping "deferred".
5. `doc/02_requirements/language/extern/extern_functions.md` — FFI spec has no
   unsafe/wrapper requirement at all.
6. **False completion claims:** `doc/04_architecture/language/memory_model_implementation.md:5`
   ("✅ COMPLETE") not corroborated in `src/compiler/`; `MEMORY_VERIFICATION_COMPLETE.md:208-210`
   attributes the checker to a Rust implementation that in fact only checks actor-mode
   compatibility.

### Bright spots (real, keep and build on)

- NLL borrow-check infrastructure: complete graph/lifetime/NLL passes, wired, on by
  default — the enforcement skeleton exists; it is starved of input (`Ref`/`Move`
  instructions), not absent.
- Atomics: genuinely backed by `std::sync::atomic` with correct orderings.
- Bounds checks: enforced on the two main execution paths (tree-walk, LLVM native).
- `HandleArena<T>`: the right generational-handle primitive already written.
- DMA buffers: allocation-identity + ownership validation already real.
- Formal side: complete Lean models for capabilities, DRF, kernel single-use.

### Gap list for implementation selection (user picks; NOT started)

Ordered by leverage (fix feeds the most properties):

- **G1. Feed the borrow checker** — emit `Move` at move sites (fixes dead
  `emit_move`) + propagate `moved_places` forward across program points + emit `Ref`
  for reference-semantic class params. Unblocks #1, #2, #3 with infrastructure that
  already exists. (Respects short-borrow-range design: scope stays narrow.)
- **G2. Param mutability enforcement** — make unannotated-param mutation a diagnostic
  (W-MC-REF-001 lint already in flight is the warn-phase of exactly this); wire `E1047`;
  prerequisite for borrow-based iterator protection (#5, #10).
- **G3. Safety-checker activation** — fix "pass never invoked" bug; construct
  `RawPointerOutsideUnsafe`/`UnsafeFfiOutsideUnsafe`; parse `unsafe:` in self-hosted
  frontend; make deny-level in MC profile (#13, #14).
- **G4. MIR-interpreter OOB trap + untyped-base bailout** — two small holes in an
  otherwise-enforced bounds story (#8).
- **G5. Mutex guard/RAII + `with lock()` + suspend-while-locked check** — replace
  manual unlock; implement the empty async mutex (#9, #11).
- **G6. Generation-handle unification** — promote `HandleArena<T>` to the canonical
  pool/arena handle; fix NVMe generation≡0; dedupe the 4 tier copies (#6, #7).
- **G7. Iterator invalidation** — after G2: borrow-based default + `CheckedCursor`
  generation alternative (#5).
- **G8. Transfer/Share structural capabilities** — Send/Sync analogue derived from
  fields; gate spawn/channel sends (#4).
- **G9. Cancellation effect annotations** — `@cancel_safe` family + channel
  cancel-atomicity implementation; promote concurrency doc from PROPOSED (#12).
- **G10. Doc truth repair** — fix the six conflicts above (false COMPLETE claims,
  "no unsafe" contradiction, blanket-unsafe capability rows). Cheap, immediate.

---

## Four-category classification (2026-07-28)

### Category 1 — ON SPEC but not fully implemented

| Item | Spec location / status | Implementation reality |
|---|---|---|
| Capability model (Shared/Exclusive/Isolated) | `borrowing.md` In Progress + complete Lean model | parsed + name-mangled only; no .spl checking pass; seed checks actor-mode only |
| Conflicting-borrow detection (E0502) | `borrowing.md` "prevents simultaneous borrows" listed pass | implemented but near-vacuous — only explicit `&`/`&mut` feed it |
| Use-after-move | borrowing/ownership spec | dead code: `emit_move` zero callers, same-point-only `moved_places` |
| Receiver/param mutability | `mutability_control.md` Planned ("checked at compile time") | metadata only; `E1047` never emitted |
| Cross-task data-race diagnostics | `concurrency_semantics.md` PROPOSED | doc itself: "not yet implemented"; runtime copy claim has no copy-on-send code |
| Copy-on-message-send | `concurrency_semantics.md:215` | prose only, no implementation |
| Cancellation semantics | REQ-CONC-004/005/006 PROPOSED | runtime `CancellationToken` only; no annotations, channel cancel-atomicity absent |
| Actor refcounting | REQ-CONC-020 | no retain/release code found |
| Unsafe boundary | `unsafe:`/`danger:` block designed; effect `@unsafe` spec'd | Rust parser only; safety pass never invoked (filed bug); 2 of 3 rules never constructed |
| Bounds checks (all paths) | language guarantee | enforced on tree-walk + LLVM native; MIR interpreter ignores OOB; untyped-base silent bailout; no freestanding trap |
| Lean proof pipeline | contract workflow spec'd | type/contract/obligation export stubs (parent audit §13.2) |
| SC-DRF memory model | report marked Complete | Lean model real; zero linkage to compiler-emitted atomics |
| Mutex/RwLock protocol | synchronization docs | wrappers exist; no guard/RAII; async mutex empty stub |

### Category 2 — NOT ON SPEC at all (missing from spec AND implementation)

| Item | Note |
|---|---|
| Iterator-invalidation protection | no spec, no mechanism, no test; compiler dodges it manually |
| Cell/RefCell interior-mutability types | absent from stdlib and requirements |
| Send/Sync analogue (Transfer/Share structural capabilities) | nothing in spec or compiler |
| Lock guards/RAII, suspend-while-locked, `@lock_level` ordering | no spec; TSan runtime detection only |
| Pointer provenance model | raw i64 addresses; no allocation-identity spec |
| FFI safe-wrapper requirement | extern spec explicitly treats FFI as ordinary calls |
| Universal generation-handle contract | `HandleArena<T>` exists as one library among 3+ ad-hoc schemes; no language contract |
| Borrow-across-suspension checking | zero coverage in spec or 55.borrow |
| Double-release / consuming-API enforcement | `@must_use` registry only; no affine spec |
| Const-by-default references | was unspec'd; NOW being added (AC-7, W-MC-REF-001 in flight) |
| Stable SymbolId / semantic doc links | was unspec'd; now spec'd by mission-critical plan, foundation landed |

### Category 3 — CONFLICTS with current design/spec

| Conflict | Evidence | Resolution direction |
|---|---|---|
| "Simple has no unsafe" vs parsed unsafe blocks | `rust_to_simple_error_mapping.md:64,329,751` vs `core.rs:829-836` | fix docs; adopt reviewed-boundary model |
| Unsafe = ALL capabilities allowed (passing req!) | `capability_system.md:222-238` | replace blanket escape with manifest-required boundary |
| `@unsafe` unchecked, no boundary obligation | `effect_system.md:134-146` | add reviewed-boundary + obligation |
| Integer-address MMIO sanctioned | `baremetal_features_examples.md:135-140` | migrate to `MmioAddress`-typed (partially exists) then `MmioRef<Reg>` |
| FFI spec: no wrapper requirement | `extern_functions.md:29-31` | MC profile: generated checked wrappers (matches parent plan §3.3) |
| Class-param mutation by deliberate design | `function_lowering.spl:250-256` (s19 bug fix) vs `mutability_control.md` claims | keep semantics; add W-MC-REF-001 warn→deny (AC-7) — enforcement layered on, not reverted |
| Mutable-by-default collections (Decision #3, Implemented) | vs borrow-based iterator protection | SOFT conflict — protect only while iterator live (Python/JS precedent); needs G2 first |
| Actor orphan-handle leak by design | `concurrency_semantics.md:466-468` | MC profile prohibits silent orphaning; base language keeps documented leak |
| False "✅ COMPLETE" claims | `memory_model_implementation.md:5`, `MEMORY_VERIFICATION_COMPLETE.md:208-235` | doc truth repair (G10) |
| Short borrowing range | user-declared DESIGN DECISION | **excluded — not a conflict, not a gap** |
| **No surface move semantics at all** (found 2026-07-28, SF1) | `mir_data.spl:337-353`; `emit_move` has ZERO callers repo-wide; red-line probe `val b = a; consume(a); print(a.x)` runs clean | **NEEDS USER DECISION — see below** |

#### C3-NEW: Simple has no move sites, so use-after-move is unreachable by construction

Found while verifying the SF1 borrow-feed lane. The NLL borrow checker exists,
is on by default, and its move logic is correct in isolation (26/26 specs). But
**no real Simple program can produce a Move fact**, because the surface language
has no move sites:

- assignment of a struct is a **copy** (structs are value types)
- assignment of a class is a **reference share**
- `iso` parses but **erases to `Infer`** at HIR lowering

`emit_move` therefore has zero callers — and its docstring now records that this
is "by DESIGN, not by omission". Wiring it up is impossible without first
creating something to wire.

This is why the borrow specs stayed green while a real use-after-move probe runs
clean: the specs hand-build `Place`/`BorrowGraph` objects and never compile
`.spl` through MIR. **Treat those specs as unit tests of the checker's logic,
not as evidence that the checker protects real code.**

**The decision this forces (not made here):** matching Rust's use-after-move
guarantee requires giving Simple surface move semantics — an affine/linear type
discipline, or making `iso` real rather than erased. That is a language-design
change with broad ergonomic consequences, in the same family as the
short-borrowing-range decision the user already resolved by keeping Simple's own
model. Options, cheapest first:

1. **Accept the difference.** Document that Simple prevents use-after-move by
   not having moves; value/reference semantics make the error unexpressible.
   Zero cost, but the checker's move path stays dead code and the Rust-parity
   claim must be narrowed accordingly.
2. **Make `iso` real.** Stop erasing it at HIR lowering; emit Move on `iso`
   binding transfer. Scoped to code that opts in, so no ergonomic tax elsewhere.
   This is the smallest change that makes the existing checker earn its keep.
3. **Full affine types.** Rust-equivalent, largest blast radius, conflicts with
   mutable-by-default collections (Decision #3) and with class reference-share.

Recommendation: **option 2** — it activates machinery that already exists and is
already correct, confines the change to an opt-in keyword that is currently
inert, and leaves the copy/share defaults untouched.

### Category 4 — other aspects where Rust is better (beyond the 11 safety properties)

Re-researched Rust advantages; Simple column is repo-verified (sweep 2026-07-28).

| Rust advantage | What Rust has | Simple status (verified) | Gap severity |
|---|---|---|---|
| **UB-checking interpreter (Miri)** | interprets MIR detecting UB (aliasing violations via Tree Borrows, OOB, uninit reads, leaks); ecosystem-standard for unsafe code CI | **missing** — sanitizers (asan/msan/tsan/lsan/ubsan) exist in-stdlib + a cert matrix script, but ZERO CI workflows run them; no UB-interpreter mode | HIGH — an MC profile without UB detection on the unsafe boundary is hollow |
| **Edition system + stability guarantee** | "stability without stagnation": 1.0 backward-compat since 2015, editions for opt-in breakage, crater runs over the whole ecosystem before releases | **missing** — no edition concept, no stability-guarantee doc (only deprecation warnings). Parent plan already assumes "next language edition" (§3.4 Stage E) that doesn't exist | HIGH — migration stages of our own plan depend on an edition mechanism |
| **Pin / self-referential futures** | sound self-referential state machines; pinning contracts | **missing** — generator state-machine transform exists, no Pin machinery; matters once borrows-across-await (G-item) lands | MED (coupled to G9/suspension safety) |
| **Aliasing model for unsafe code** | Stacked/Tree Borrows: a defined model unsafe authors test against | **missing** — no defined aliasing model for raw-pointer code | MED — needed before native encoders are "certified" |
| **Supply chain: SBOM + dep audit** | cargo audit/vet/deny, lockfile discipline, RustSec advisory DB | **partial** — signing/trust/verify + integrity exist; NO SBOM (no spdx/cyclonedx hits), no CVE audit equivalent. Parent plan's release criteria already require SBOM | HIGH for release gate |
| **Platform tier policy** | documented tier 1/2/3 with per-tier guarantees | **partial** — 27 CI workflows with real OS matrix, but no tier policy doc, single released artifact tree | MED |
| **Package registry (one ecosystem)** | cargo + crates.io: one client, one registry, semver-resolved | **partial + fragmented** — TWO clients (`src/app/pkg/`, `src/app/snpm/`) + OCI registry backend, no live public registry; fragmentation is itself the defect | MED |
| **Const generics + CTFE** | full const generics, miri-backed const eval | **partial** — const folding + limited const generics in HIR; no comptime | LOW-MED |
| **Coverage-guided fuzzing** | cargo-fuzz/libFuzzer, OSS-Fuzz integration | **partial** — corpus fuzz tests + cert scripts, not coverage-guided, no harness generator | MED |
| **Formal spec + qualified toolchain** | FLS + Ferrocene (ISO 26262/IEC 61508 qualified rustc), safety manual, known-problems process | **partial** — Lean models + planned SAFETY_MANUAL/QUALIFICATION_PLAN (docs not yet written); no qualification evidence | HIGH (it IS the mission-critical target) |
| **Trait solver depth** | chalk-style canonicalization, GATs, specialization discipline, years of coherence hardening | **exists-mature but simpler** — dedicated 25.traits phase w/ coherence+orphan checks; no GAT/canonicalization evidence | LOW — simpler may be fine; needs conformance tests |
| **Proof/verification ecosystem** | Kani, Creusot, Prusti, Aeneas, Verus — several independent maturing tools | **partial** — integrated Lean pipeline is architecturally AHEAD of Rust, but generator stubs (parent §13.2) mean Rust's external tools currently deliver more working verification | HIGH until C2-C5 land |
| **Error-message polish** | renowned diagnostics + `--explain` + rustc dev guide culture | **exists-mature** — 179 structured codes, spans/help/suggestions, i18n tables; parity plausible, needs no new architecture | LOW |
| **Incremental compilation** | query-based incremental, sccache | **exists-mature** — incremental_builder + module caches | LOW (parity) |
| **Macros/hygiene** | proc macros + declarative, hygiene | **exists-mature** — registry/expander/hygiene pipeline | LOW (parity) |

**Where Simple is already at parity or ahead (verified):** incremental compilation,
structured diagnostics + i18n, macro hygiene pipeline, trait coherence phase, integrated
(if stubbed) proof pipeline, OCI-signed package registry design, in-stdlib sanitizers
written in Simple itself.

**Category-4 gaps that fold into existing plan lanes:** SBOM → release-gate lane;
Miri-equivalent → G3+G4 extension (UB checks on the MIR interpreter it already has);
edition system → prerequisite for §3.4 Stage E migration; Ferrocene-class evidence →
SAFETY_MANUAL/QUALIFICATION_PLAN docs already in §9. New items with no lane: Pin,
aliasing model for unsafe, registry unification, platform-tier policy.

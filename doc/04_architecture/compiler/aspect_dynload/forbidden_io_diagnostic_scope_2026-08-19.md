# E-APACK008 "attempted lazy I/O in forbidden execution context" — Scope Analysis

Date: 2026-08-19. Status: SCOPING ONLY — no implementation in this doc.

Inputs:
- Design: `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md` (§19 lines 1402-1428, §21 lines 1488-1540)
- Audit: `doc/09_report/aspect_pack_field_diagnostic_checklist_2026-08-19.md` (E-APACK008 row, line 277; summary lines 279, 332, 388, 437)
- Implementation: `src/lib/common/aspect_pack.spl`

## 1. What exactly does the design forbid, and during which phase?

The diagnostic itself is defined only by its one-line entry in §21 (design line 1524):

> `E-APACK008 attempted lazy I/O in forbidden execution context`

The governing rules are §19 "Mission-Critical Profile". The policy block (lines 1404-1415) declares:

> ```
> aspect_policy:
>   dynamic_attach: deny
>   unload: deny
>   lazy_io_after_start: deny
>   ...
>   activation: [static, startup]
> ```

And the prose rules (lines 1417-1425), quoted verbatim:

> - All enabled aspects are fixed before operational state.
> - No first-use disk I/O in real-time/interrupt/noalloc contexts.
> - `try_facet<T>()` is permitted after startup; lazy-loading `facet<T>()` is not.

So the forbidden act is **first-use (lazy) pack I/O — opening a pack file, decompressing a module payload, mapping pages — triggered by a `facet<T>()` acquisition**, and the forbidden phase is stated in TWO overlapping but non-identical formulations:

- (a) *temporal*: after startup / after the application reaches "operational state" (`lazy_io_after_start: deny`);
- (b) *contextual*: inside "real-time/interrupt/noalloc contexts", regardless of clock phase.

**Ambiguity, stated rather than resolved:** the design does not say whether E-APACK008 covers (a), (b), or their union. Formulation (a) forbids lazy I/O anywhere after a global phase transition; formulation (b) forbids it in specific execution contexts even during startup. Nothing in §19 or §21 defines "operational state" as a runtime-observable event, nor names the component that flips it. A later implementer must pick the union or split the code; the design text does not decide.

## 2. Which component can observe a violation? (search results)

Searched for existing enforcement (2026-08-19, owned code only, vendor excluded):

- `lazy_io` / `lazy_io_after_start` across `src/**/*.spl`: **zero hits** — the §19 policy key is parsed nowhere; no `aspect_policy` reader exists.
- `forbidden.*I/O`, `io_forbidden`, `no_io`, `forbid_io` across `src/`: only vendored Rust (`portable-atomic-util`) and an unrelated DMA gate (`src/os/drivers/dma/dma_safety_gate.spl:63`). Nothing aspect- or phase-related.
- `interrupt context` / `irq_context` / `in_interrupt` / `noalloc context` in `src/lib`, `src/runtime`, `src/compiler`: one hit — `src/compiler/35.semantics/noalloc_checker.spl:173` ("Classification of why an @noalloc context was violated").
- "phase" markers in `src/lib/nogc_async_mut_noalloc/execution`: none. No scheduler phase marker, no startup/operational phase flag anywhere found.
- `facet<` call sites outside `aspect_pack.spl`: **zero** — `facet<T>()` acquisition, the act that would trigger lazy I/O, is not implemented anywhere yet.

What DOES exist (nearest neighbors):

- **`@noalloc` static checker** — `src/compiler/35.semantics/noalloc_checker.spl` (compiler-owned semantic pass, lines 1-10). It classifies violations as DirectAlloc / TransitiveCall / **FamilyImport** (line 176), where FamilyImport (line 10) rejects "call into an allocating runtime family per the manifest". This is exactly the machinery shape (b) needs: a call into the pack-loading family from an `@noalloc`/interrupt context is statically detectable the same way an allocating call is. It does not currently model I/O at all — `allocates` is its only axis.
- **Startup pre-binding** — `src/lib/common/aspect_pack.spl:931` `apk_activate_startup` ("Bind every `startup` route before the application publishes itself"), with `apk_catalog_startup_keys_v1` at line 676 citing design §9.4. This is the *avoidance* half of §19 rule 1 (aspects fixed before operational state) and already exists; what does not exist is anything that detects a lazy load attempted *after* that point.
- The audit's verdict stands confirmed: `aspect_pack.spl` has "No context guards" (checklist line 277) and cannot have them — it is a passive container/loader library with no view of scheduler state.

**Conclusion: no I/O-phase enforcement of any kind exists today.** The observing components would have to be (a) the runtime/scheduler, which alone knows "operational state" — a concept that itself has no marker yet; and (b) the compiler semantics layer (35.semantics), which already walks call graphs for context violations.

## 3. Statically or dynamically enforceable?

**Both, split by formulation:**

- **(b) forbidden contexts — statically enforceable, and statically is strictly better.** "`facet<T>()` (lazy) reachable from an @noalloc/interrupt function" is a call-graph property, the same class the noalloc checker already proves. A static reject at compile/weave time (`activation: [static, startup]` is a build-time policy) prevents the violation instead of reporting it after a real-time deadline was already blown. Note lazy pack I/O also *allocates* (decompression buffers), so even today's noalloc checker would incidentally flag the transitive path once `facet<T>()` exists — but as an allocation diagnostic, not E-APACK008.
- **(a) after-start — dynamically only, and only partially statically.** Whether a given `facet<T>()` call executes before or after "operational state" is not in general decidable statically (the same function may run in both phases). Runtime enforcement needs: a phase flag set at publication time (the natural site is right after `apk_activate_startup` succeeds), checked at the top of the lazy-acquire path (`_apk_acquire_facet`), erroring E-APACK008 instead of doing I/O. The flag's owner must be the runtime/scheduler; `aspect_pack.spl` could *check* a flag handed to it, but cannot *set* one.
- A complete E-APACK008 is therefore a **two-layer diagnostic**: static reject where provable (compiler, cheap, mission-critical-profile builds), plus a runtime fail-closed guard for the residue.

## 4. Recommendation: DO-NOT-BUILD-YET

Reasoning:

1. **The triggering feature does not exist.** There are zero `facet<T>()` call sites in the tree; lazy facet acquisition is not implemented as a language/runtime surface, only as the library primitive `_apk_acquire_facet`. A guard on a path nothing calls is unverifiable dead code (violates "no unused code").
2. **The precondition concept does not exist.** No component defines or marks "operational state"/publication; building the runtime check first would force inventing the phase model ad hoc inside a library, which is exactly the layering error the audit rejected.
3. **The policy plumbing does not exist.** No `aspect_policy` / `lazy_io_after_start` parser exists anywhere; E-APACK008 is only meaningful under a profile no build can yet declare.
4. **Static half has a clear future home.** When built: the static reject belongs to **`src/compiler/35.semantics`** (extend the noalloc-checker pattern with an I/O-family axis, keyed off the mission-critical `aspect_policy`); the runtime flag belongs to the **runtime/scheduler layer that owns application publication**, with `aspect_pack.spl` accepting at most a caller-supplied "lazy loads permitted" bit at `_apk_acquire_facet`. Owning layer if forced to name one: 35.semantics for the buildable majority.

Build trigger: revisit when EITHER `facet<T>()` sugar lands in the language surface OR an `aspect_policy` reader lands in the build pipeline — whichever first. Until then E-APACK008 stays a reserved code (design §21 line 1524) with this doc as its scope record.

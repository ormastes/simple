# Domain Research — Stronger Types: Unified `unit`, Effects, Session/Typestate, LSP

**Date:** 2026-11-05
**Status:** primary-source design inputs, consolidated from `doc/05_design/stronger_types_unified_unit.md` §13/§15.2. No new web verification this pass; each entry is a primary source cited by the design. Performance results from research prototypes are not predictions for Simple.

## Adopted inputs

| Source | Idea adopted for Simple | Kept out of the normal fast path |
|---|---|---|
| F# Units of Measure — https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/units-of-measure | Compile-time dimensional checking with erased unit metadata; normalized dimension metadata + type-directed diagnostics | No new solver; real scaling still costs arithmetic |
| Koka, row-polymorphic effect types (Leijen 2014) — https://www.microsoft.com/en-us/research/publication/koka-programming-with-row-polymorphic-effect-types-2/ | Infer possible behavior, compose through calls; conservative summaries on existing effect rows | No algebraic-effect handler runtime merely to track I/O |
| Flux: Liquid Types for Rust (PLDI 2023) — DOI 10.1145/3591283 | Refinements compose with ownership; inference reduces annotations in selected cases | SMT/liquid inference only in debug/invest/ci modes |
| Ferrite: session types in Rust (ECOOP 2022) — https://arxiv.org/abs/2009.13619, https://ferrite-rs.github.io/ferrite-book/02-main-concepts/01-protocols.html | Generic continuation types for protocol fidelity over typed channels | Shared/multiparty verification and global-progress proofs |
| Typestate via Revocable Capabilities (PLDI 2026) — DOI 10.1145/3808323; artifact https://zenodo.org/records/19614655 | Resource-specific permission dependencies tracking state through aliases | Full higher-order/shared revocation (prototype has documented unsound gaps — mutable fields, polymorphic values, revocations that silently do not take effect); Simple must reject/conservatively downgrade such cases |
| Thrust: prophecy-based refinement for Rust (PLDI 2025) — DOI 10.1145/3729333 | Propagate refined facts through mutable borrow release; modular invariant reasoning | CHC solving / prophecy-based deep verification |
| RefinedRust (PLDI 2024) — https://plv.mpi-sws.org/refinedrust/ | Foundational verification must cover unsafe implementations behind safe APIs | Proof-assistant verification of complex runtimes |
| Rust `PhantomData` — https://doc.rust-lang.org/std/marker/struct.PhantomData.html | Zero-size markers still carry ownership/lifetime significance | No runtime marker objects for static identity |
| Rust Reference, behavior not considered unsafe — https://doc.rust-lang.org/reference/behavior-not-considered-unsafe.html | Comparison boundary: safe Rust does not guarantee absence of deadlock, leaks, or logic errors | — |
| LSP 3.18 spec — https://microsoft.github.io/language-server-protocol/specifications/lsp/3.18/specification/ + codeAction.md | Standard diagnostics/hover/inlay/codeAction/resolve/versioned WorkspaceEdit; negotiate client capabilities | Simple semantic queries (AST search, effect paths, unit migration) are negotiated extensions, not standard methods; multi-file WorkspaceEdit is not atomic |

## Deferred explicitly

General higher-order theorem proving in everyday compilation; a new dependent/session/capability language surface; copying the revocable-capability prototype wholesale; global deadlock or distributed-correctness claims from local types; solver-driven rewrites of business/protocol behavior; universal elimination of runtime checks at foreign/concurrent/device boundaries.

## Design consequences for release/1.0.0 (grounded in local research)

1. **Frontend-first implementation**: the unified `unit` grammar must land in the self-hosted frontend (`src/compiler/10.frontend`), which today parses only `newunit`/`newtype` (both lowered to single-field structs with side-table metadata at `core/types.spl:938-975`). The Rust seed's richer `unit` forms are bootstrap-only.
2. **Effect hardening is repair, not invention**: all five gaps from the design audit are confirmed live (`inference_effects.spl:106-192`); fix fail-open behavior, add completeness/unknown tracking, and do not grow a third effect system alongside `param_effects/` and `type_system/effects.spl`.
3. **Payload-typed endpoints are green-field**: no `Sender<T>`/`Receiver<T>` exists; `Channel.send` silently discards admission status — making rejection observable is the first required semantic change.
4. **Tooling reuses existing surfaces**: compiler-native `CompilerQueryContext` (`src/compiler/90.tools/query_api.spl`), CLI `query.spl` routing, MCP `tool_table.spl`, LSP handlers in `src/lib/nogc_sync_mut/lsp/`.

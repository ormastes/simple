# Semantic Build Cache (v2) — developer guide

**Read this first: none of what follows is wired into your build yet.**

As of 2026-08-10 the semantic build cache v2 modules exist, are tested, and are
formally modelled. The legacy cache (`.build_cache.sdn` plus `.build/mir_cache/`)
still makes **every** build decision. The one v2 code path a normal build can
reach is **shadow mode** — opt-in via `SIMPLE_CACHE_V2_SHADOW=1`, which runs v2
lookup/publish/byte-compare alongside the legacy path in the incremental driver
and prints one summary line (hits/misses/mismatches/errors). Shadow mode never
changes build output; a v2 failure is counted, never propagated.

This guide documents what is in the tree and what is deliberately not, so you can
tell the difference. It will grow a "how to use it" section when there is one.

---

## What exists today

| Capability | State | Reachable from `bin/simple`? |
|---|---|---|
| SHA-256 action identity + CAS | implemented, tested | **No** — zero callers |
| L1 workspace / L2 machine tier router | implemented, tested | **No** |
| Storage watermarks, leases, GC | implemented, tested | **No** |
| Remote-main lookup | read-only stub, no transport | **No** |
| Remote-main writes | **deliberately disabled** | **No — and must stay that way** |
| Shadow mode (v2 alongside legacy, compare-only) | implemented, opt-in env | **Yes** — `SIMPLE_CACHE_V2_SHADOW=1`; recompiled modules only; coarse key (see gaps) |
| Block dependency cache (C5 slice 1) | keys + worklist + manifests, in-memory | **No** — consumed by nothing yet |
| CI promotion gateway (C9 slice 1) | local validator + main-only workflow | CI-only; no remote write step exists |
| AOP invalidation groups | implemented, mostly conservative | **No** |
| `CompileInterfaceDigest` | compute-and-log | **No** |
| Lean proofs of the identity model | 74 theorems, green | Yes — via the gate script |
| `simple cache …` CLI | **not implemented** | **No** |

The CLI surface described in the design doc (`simple cache status/explain/gc/…`)
is a specification, not a shipped feature. Do not cite it in other docs as though
it works.

## What you can actually run

The formal gate is the one thing here that is genuinely runnable and meaningful:

```bash
sh scripts/check/check-cache-protocol-formal.shs
```

Verdict is the **last line** of stdout and the exit code is authoritative:

| verdict | exit | meaning |
|---|---|---|
| `PASS — …` | 0 | proofs built, no trust bypass, coverage complete, regeneration clean |
| `FAIL — …` | 1 | a proof, coverage, or regeneration check failed |
| `ERROR — nothing was checked` | 2 | could not find the project; **not** a pass |

Capture the exit code directly — `… | tail -1; echo $?` gives you `tail`'s status,
not the guard's.

The unit specs:

```bash
bin/simple test test/01_unit/compiler/cache_v2/tier_router_spec.spl   # 6
bin/simple test test/01_unit/compiler/cache_v2/gc_spec.spl            # 8
bin/simple test test/01_unit/compiler/cache_v2/aop_group_spec.spl     # 12
bin/simple test test/01_unit/compiler/cache_v2/promotion_spec.spl     # 33
bin/simple test test/01_unit/compiler/interface_compat/compile_interface_spec.spl  # 7
```

Trust only the `SPEC FILE VERDICT … executed=N` line with N > 0. `simple test`
given an **absolute** path runs nothing and still exits 0.

## Things you need to know before touching this

**The cache decides what may be reused instead of recomputed.** A false hit is a
silent miscompilation — wrong bytes served with confidence. A false miss just
costs time. Every ambiguity resolves toward recomputation, and that asymmetry is
why several parts here deliberately over-invalidate.

**Exact-key lookup only.** If you are ever tempted to add a "close enough"
fallback so more things hit, don't. That is a correctness bug wearing a
performance costume.

**Your branch does not affect cache identity.** Branch, commit, and CI run are
recorded as *provenance* for deciding what may be published, never as part of the
key. Two identical builds on different branches are supposed to share results.

**You cannot publish to the shared main cache from your machine.** That is
enforced structurally, not by configuration, and there is intentionally no flag
to override it.

## Known gaps (do not rediscover these)

Full list: `doc/08_tracking/bug/cache_v2_first_milestone_known_gaps_2026-08-10.md`.
The ones most likely to bite:

- **All verification used the Rust seed binary**, not the self-hosted compiler.
  GREEN here does not prove self-hosted correctness.
- `CompileInterfaceDigest` is missing generic constraints, effects, and parameter
  passing modes, because `ApiSurface` does not carry them. A generic-bound change
  may not move the digest — that is an under-invalidation risk, and the reason it
  drives no decisions.
- The `abi`/`semantic`/`link` digests are placeholder re-hashes. They mean nothing.
- Free-space admission is scoped to the cache's own byte budget; it cannot see
  that the *disk* is filling from some other cause.
- **The SMF header is not wire-identical between the Simple and Rust
  implementations** (96 B padded vs 128 B packed, fields shifted by 4 from offset
  20 onward). See
  `doc/08_tracking/bug/smf_header_wire_layout_diverges_rust_vs_simple_2026-08-10.md`
  before touching any SMF layout. Do not change either side unilaterally.

## Where the real documentation lives

- Design (normative): `doc/05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md`
- Waves and ownership: `doc/03_plan/compiler/cache/semantic_incremental_build_v2_plan_2026-08-09.md`
- Frozen field contract: `doc/03_plan/compiler/cache/c0_schema_freeze_2026-08-09.md`
- Agent/LLM notes: `doc/00_llm_process/feature_expert/cache_tiering/skill.md`,
  `doc/00_llm_process/layer_expert/driver_cache/skill.md`

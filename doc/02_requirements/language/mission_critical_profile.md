# Mission-Critical Assurance Profile — Requirements

**Status:** DRAFT-NORMATIVE (rules land phased; each rule names its phase)
**Date:** 2026-07-28
**Research base:** `doc/01_research/language/simple_vs_rust_mission_critical_2026-07-27.md`,
`doc/01_research/language/simple_vs_rust_safety_property_audit_2026-07-28.md`
**Plan:** `doc/03_plan/agent_tasks/mission_critical_robustness_parallel_agents_2026-07-27.md`

## Profile position

`mission-critical-v1` is a fourth strictness profile above `moderate`/`lib`/`reliable`.
Its rules are release requirements, not optional diagnostics. It is **fail-closed**: a
missing checker, missing external tool, unverifiable claim, or stale evidence reports
**blocked**, never passed.

## REQ-MC-001 — Semantic public types (phase: Batch 1, checker landed)

No primitive leaf (i8..i64, u8..u64, f32, f64, **bool** — canonical table
`compiler.semantics.lint.primitive_types`) reachable through the normalized type graph
of a public or mission-critical interface. Aliases, Option/Result/containers, tuples,
enum payloads, callbacks do not hide primitives. Wrap in `newunit`, unit, enum, Option,
Result. No pure-math exemption in this profile. `extern fn` raw signatures allowed only
beneath generated checked wrappers.

## REQ-MC-002 — Const-by-default references (phase: WARN now, deny at v2 — user decision 2026-07-28)

Parameters and references are immutable by default. Mutation opt-ins: `mut` parameter
annotation, `me` receiver. Rule `W-MC-REF-001 const_ref_default` warns in all tiers now;
escalates to deny in this profile at v2. Receiver rule (`me`) is language-wide already.

## REQ-MC-003 — Enum contracts (phase: Batch 3+, needs payload metadata)

`@condition` two-state enums for boolean domains; `@closed` enums (exhaustive matches,
no wildcard in MC code, invalid discriminants rejected on decode); `@evolving(repr,
unknown)` enums (unknown values preserved + round-trippable).

## REQ-MC-004 — Unsafe boundary (phase: SF2 in flight)

`unsafe:`/`danger:` blocks are capability-scoped, not blanket:
`@unsafe(reason: text, capabilities: [raw_ptr | ffi | mmio | ...])`. In this profile a
boundary requires reason + reviewer manifest. Raw-pointer externs and FFI calls outside
an unsafe boundary are diagnostics (warn baseline, deny here). Supersedes the
blanket "unsafe = all capabilities" rule in `di/capability_system.md`.

## REQ-MC-005 — Memory-safety enforcement (phase: SF1/SF3/SF5 in flight)

Use-after-move rejected across program points; conflicting borrows rejected (short
borrow range per design decision — narrow scope is intended); bounds enforced on ALL
execution paths incl. MIR interpreter; generation-counted handles for pooled/arena
resources with real generation stamping (generation≡0 arenas are a defect).

## REQ-MC-006 — Synchronization + interior mutability (phase: SF4 in flight, rest Batch 3)

Lock access through RAII guards / `with_lock` closures — manual unlock deprecated;
async-tier locks implemented, never empty stubs. Later: suspend-while-holding-lock
diagnostics, lock-level ordering, Transfer/Share structural capabilities for cross-task
types, cancellation-effect annotations on suspending operations.

## REQ-MC-007 — Proof coverage (phase: Lean lane C2-C7)

Certified closure: no `sorry`/`admit`/undeclared axioms (token-aware gate, landed);
per-symbol proof status; trusted assumptions only via signed manifest; unsupported
constructs fail compilation.

## REQ-MC-008 — Semantic traceability (phase: SymbolId foundation landed)

Stable SymbolId links (`spl:fn@module.path~fingerprint`) for maintained docs; line-based
`.spl#L...` links denied in this profile (`W-DOC-AST-001`); renames emit redirects,
ambiguity errors — never silent retargeting.

## REQ-MC-009 — Codegen truth (phase: D4 slice landed, registry Batch 3)

No silent scalar/unsupported-instruction fallback; unverified lowering fails the build;
layout from the canonical type mapper (8-byte assumptions are defects); ISA coverage
generated from registry, never hand-maintained prose.

## REQ-MC-010 — Evidence + release (phase: release-gate lane)

Reproducible artifacts, SBOM, bootstrap evidence, fresh proof/conformance evidence,
known-problem register, trust manifest. Stale or missing evidence blocks release.
Only the aggregate gate emits "production ready".

## REQ-MC-011 — No bare primitives in internal code (phase: WARN in MC now, deny at v2 — user decision 2026-07-28)

Firmware-style rule: primitives are prohibited not only at interfaces (REQ-MC-001) but
in **all internal code** of a mission-critical package. Every local binding carries a
domain type:

```simple
val timeout: DurationMs = 1        # OK — explicit domain annotation
val timeout = 1_s                  # OK — newunit suffix literal types it
val n = 1                          # W-MC-VAL-001 — bare primitive local
val n: i64 = 1                     # W-MC-VAL-001 — explicit primitive annotation
```

Rule `W-MC-VAL-001 bare_primitive_internal`. Levels: `allow` in
moderate/lib/reliable (would flood non-MC code), **warn** in `mission-critical`
profile now, **deny** at profile v2 — the warn phase exists for backward
compatibility during migration. Representation boundaries (REQ-MC-004 unsafe /
`@representation_boundary`) are exempt, as are loop induction variables in `for i in
range` (follow-up decision) and untyped bindings initialized from typed expressions
(the expression's type governs — checked by REQ-MC-001's semantic checker once wired).

## REQ-MC-012 — Profile-aware execution (user design, recorded 2026-07-28)

Strictness profiles are not lint-only: the **interpreter is a first-class execution
mode** (default engine for development/test use), and `bin/simple run`/`bin/simple test`
accept the profile axis so tests execute UNDER a chosen profile:

```bash
bin/simple test path/spec.spl --profile=moderate         # baseline
bin/simple test path/spec.spl --profile=lib
bin/simple test path/spec.spl --profile=mission-critical # MC checks active at runtime
```

Semantics: the profile selects which diagnostics are live during execution (lint levels
applied pre-run, fail-closed per profile) and which runtime checks are enabled (bounds
trap severity, MIR-interpreter trap mode, sanitizer hooks as they land). A package's
`simple.sdn` `[lints] profile=` sets its default; the CLI flag overrides per run.
Verified 2026-07-28: NO profile plumbing exists today in run/test paths — lint only.
Status: NOT IMPLEMENTED — Batch 3 lane.

**Two orthogonal axes (user decision 2026-07-28):** engine and profile compose freely.

```
--engine=interpreter|jit|native      # interpreter = DEFAULT for run/test (dev loop)
--profile=moderate|strict|robust|critical
```

- The interpreter is the named first-class default engine for `run`/`test`; JIT and
  native are opt-in (JIT for speed, native for release artifacts). Note: this changes
  the current default (JIT) — recorded as intended; perf-sensitive suites may pass
  `--engine=jit` explicitly.
- `moderate` is NOT "interpreter mode" — any profile runs on any engine.
- **Default pairing (user confirmed 2026-07-28, revised same day):** profile
  resolution = `--profile` flag > `simple.sdn [lints] profile=` > engine default,
  where interpreter→`moderate`, jit→`moderate`, and **compiler/loader (native
  build + module loading)→`robust` at WARN severity** — robust's full rule set
  runs but reports as warnings during the migration window; escalation of those
  warnings to errors is a later backward-compatibility step (profile v2), same
  phasing pattern as REQ-MC-002/011. Bare `bin/simple run x.spl` =
  interpreter+moderate (scripting-like; safety still on underneath). For packages
  pinned `robust`+ in `simple.sdn`, the CLI flag may RAISE but never LOWER the
  profile (fail-closed).

## Profile ladder rename (user approved 2026-07-28)

| New | Old (deprecated alias, warn once) | Contract |
|---|---|---|
| `moderate` | `moderate` | safety always on; discipline relaxed |
| `strict` | `lib` | + public-API discipline at warn |
| `robust` | `reliable` | Rust-level enforced: all escapes denied |
| `critical` | `mission-critical` | > Rust: proofs, evidence, internal-primitive ban, fail-closed |

Old spellings keep parsing with a deprecation warning; removal is an edition decision.
All rule phase notes in this doc map onto the new names (`mission-critical` → `critical`).

## Non-goals / design decisions honored

- Short borrowing range: intended design, not a gap.
- Class-param reference semantics (s19): kept; enforcement layers on via REQ-MC-002.
- Mutable-by-default collections (Decision #3): kept; iterator-liveness restriction only.
- Base (non-MC) profiles keep current ergonomics; this profile is opt-in per package.

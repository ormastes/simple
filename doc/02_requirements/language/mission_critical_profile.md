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
~~Verified 2026-07-28: NO profile plumbing exists today in run/test paths — lint only.
Status: NOT IMPLEMENTED — Batch 3 lane.~~

**Corrected 2026-08-07.** Partial plumbing DOES exist and this paragraph was stale:
`run` sets `SIMPLE_SAFETY_PROFILE` around the call
(`src/app/io/_CliCommands/handler_commands.spl:177`) and the test runner sets it for
the subprocess (`src/lib/nogc_sync_mut/test_runner/test_runner_config.spl:188`).

What is still NOT implemented is the part that makes it trustworthy:

- **No authoritative in-process state.** `SIMPLE_SAFETY_PROFILE` is a process-global
  env var. The driver re-reads it per call (`80.driver/driver_safety_severity.spl:62-63`),
  while the interpreter **latches it once** at `eval_init`
  (`10.frontend/core/interpreter/eval_decls.spl:297`) and cannot observe a later change.
  `ProjectContext.active_profile` (`80.driver/project.spl:56`) is never set —
  `set_active_profile` (`:133`) has zero callers.
- **Project-level pinning does not work at all.** `load_from_sdn` (`project.spl:81-90`)
  parses and then returns defaults. All three TOML-ish `[lints] profile =` scanners
  (`90.tools/lint/_LintMain/config_and_model.spl:335-352`, `handler_commands.spl:114-131`,
  `test_runner_config.spl:48-71`) always return `""`, because no `simple.sdn` in the
  repo carries a `lints` key and there is no repo-root manifest. The documented native
  convention is indent/colon (`doc/06_spec/system/compiler/modules/tooling/formatting_lints.md:345,:438`),
  which nothing reads.

Status: PARTIAL — env-var propagation only; typed policy resolution and SDN pinning
tracked as WP-3/WP-4 in
`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`.

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

## REQ-MC-023 — No unwrapped foreign resource (phase: WARN in critical now, deny at v2 — user decision 2026-08-07)

Firmware-style rule, same shape as REQ-MC-002/011: a raw opaque handle
acquired from an `extern fn`/SFFI boundary (typically a bare `i64`, per the
Opaque Handle Pattern in `doc/07_guide/platform/ffi/sffi.md`) must not be
passed around, stored, or returned without being wrapped in an owning Simple
type whose release is a consuming drop — either the `resource R` declaration
(`doc/04_architecture/language/resource/resource_declaration_architecture_2026-08-06.md`,
`doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md`,
**proposed, not implemented** — see that phase note below) or, until `resource`
lands, a hand-written class whose only field is the handle and whose `close`/
drop method calls the paired release extern exactly once.

**Wrapped (OK):**

```simple
@sffi(prefix: "rt_file", invalid: -1)
resource File

fn read_config(path: text) -> text:
    val file = File.open(path)?      # owning wrapper; auto-release on scope exit
    file.read_all()
```

```simple
# Until `resource` lands: hand-written wrapper is also compliant.
class Database:
    handle: i64                       # private field, not re-exposed

    static fn open(path: text) -> Database:
        Database(handle: spl_db_open(path))

    fn query(sql: text) -> text:
        spl_db_query(self.handle, sql)

    fn close():
        spl_db_close(self.handle)     # release fires exactly once
```

**Unwrapped (flagged):**

```simple
extern fn rt_file_open(path: text) -> i64
extern fn rt_file_close(handle: i64) -> bool

fn read_config(path: text) -> text:
    val handle = rt_file_open(path)   # W-MC-RES-001 — bare handle escapes the FFI call site
    val text = read_from(handle)      # handle threaded through app code unwrapped
    text

fn open_two(a: text, b: text) -> (i64, i64):
    (rt_file_open(a), rt_file_open(b))  # W-MC-RES-001 — raw handles returned to caller
```

Rule `W-MC-RES-001 unwrapped_foreign_resource`. Levels: `allow` in
moderate/strict/robust (would flood non-critical FFI glue), **warn** in
`critical` profile now, **deny** at profile v2 — same warn-then-deny phasing
as REQ-MC-002 (`W-MC-REF-001`) and REQ-MC-011 (`W-MC-VAL-001`), and the same
user decision date pattern.

**Exemptions**, mirroring REQ-MC-011's `@representation_boundary` carve-out:

- The `extern fn` declaration itself, and the single call expression that
  invokes it to acquire or release the handle — the rule flags the handle
  *escaping* that call site, not the call.
- Code inside an `@unsafe(reason: text, capabilities: [ffi])` boundary
  (REQ-MC-004) or a generated SFFI adapter module (`90.tools/sffi_gen`
  output) — this is the representation/FFI boundary carve-out; raw handles
  are expected there.
- The `resource` declaration's own generated adapter body once Phase 1 of
  the design lands (it is the wrapper).

**Enforcement phase:** compile-time lint, `critical` profile only (same
severity-table mechanism as `W-MC-REF-001`/`W-MC-VAL-001`, driver
`80.driver/driver_safety_severity.spl`, lint `90.tools/lint/_LintMain/config_and_model.spl`).

**Status: SPECIFIED, NOT IMPLEMENTED.** No `W-MC-RES-001` checker exists in
`src/compiler/90.tools/lint` or elsewhere as of this writing, and it has no
entry in the lint registry (`lint_checks.spl`) the way `W-MC-VAL-001` does not
either — REQ-MC-011 is itself only a rule-name reservation, not a landed
checker; this rule is the same kind of reservation. It additionally depends on
the `resource` declaration (Phase 1, not yet implemented — see
`doc/04_architecture/language/resource/resource_declaration_architecture_2026-08-06.md`)
for the primary wrapped-form example to be checkable as `resource`-typed
rather than only as the hand-written-class fallback. Per REQ-MC-012's
reachability caveat, even a landed checker enforces nothing through
`bin/simple` until stage-3 self-host unblocks — `bin/simple` today is the
Rust seed, which has no lint code for this family at all. The
`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`
premises table (row 12b: "the enemy is reimplementation, not absence")
applies here too — if a WARN-only text heuristic for this rule is ever added
ahead of a real semantic checker, it must be named as the twin that dies when
the semantic checker lands, not kept alongside it.

## Non-goals / design decisions honored

- Short borrowing range: intended design, not a gap.
- Class-param reference semantics (s19): kept; enforcement layers on via REQ-MC-002.
- Mutable-by-default collections (Decision #3): kept; iterator-liveness restriction only.
- Base (non-MC) profiles keep current ergonomics; this profile is opt-in per package.

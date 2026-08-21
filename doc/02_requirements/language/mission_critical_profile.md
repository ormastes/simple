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

## REQ-MC-013 — Canonical assurance-policy resolution (phase: compile-time, typed state — IMPLEMENTED 2026-08-07)

Profile resolution is unified: five callsites (lint parser, driver severity engine, `run`
command, test runner, interpreter) all delegate to a single canonical resolver
(`src/compiler/00.common/assurance/policy.spl:policy_for_name_and_cli_flag`) that
applies precedence: CLI flag > `simple.sdn` project pinning > engine default (interpreter→`moderate`,
jit→`moderate`, compiler/loader→`robust`-at-WARN). The resolver returns a typed
`ResolvedAssurancePolicyV1` with `(name, severity_projection, is_deny_tier)` for all
accepted spellings (profile names + deprecated aliases). Deprecated aliases (`mission-critical`,
`mission_critical`, `mission_critical_internal`, `mission_critical_v1`) warn once per
invocation; the canonical names are `moderate`, `strict`, `robust`, `critical`.

`SIMPLE_SAFETY_PROFILE` env var is demoted to subprocess serialization only (driver re-reads
it, test runner passes it to subprocess, interpreter no longer latches it at `eval_init`).
Instead, the interpreter receives a typed policy via `eval_apply_assurance_profile`
(`src/compiler/10.frontend/core/interpreter/eval_decls.spl:304-312`), removing the
latch-once defect.

**Enforcement phase:** compile-time; policy resolution is wired at all five sites and is
fail-closed (unrecognized profile name is an error, not a fallback).

**Status:** IMPLEMENTED. Landed `4817dd06f0f`; unit test `test/01_unit/compiler/assurance/policy_five_site_convergence_spec.spl`, 24/24.

## REQ-MC-014 — Project-level assurance-profile pinning via SDN (phase: compile-time, typed state — IMPLEMENTED 2026-08-07)

A `simple.sdn` manifest can pin a profile via `lints:` / `profile: <tier>`:

```
project:
  name: my_package
  source_root: src

lints:
  profile: critical
```

The canonical form is indent/colon, not TOML-ish `[section]` syntax. `ProjectContext.load_from_sdn`
parses the manifest and calls `set_active_profile(profile_name)` at `src/compiler/80.driver/project.spl:81-90`,
setting `active_profile` (`src/compiler/80.driver/project.spl:56`) to a typed `ResolvedAssurancePolicyV1`.
The CLI `--profile` flag may **raise** the pinned tier but never **lower** it (fail-closed). Three
dead TOML-ish scanners in `config_and_model.spl:335-352`, `handler_commands.spl:114-131`,
`test_runner_config.spl:48-71` were deleted; no compatibility path kept.

**Enforcement phase:** compile-time and integration; the driver validates the SDN syntax at load time
and enforces the raise-only constraint at CLI resolution.

**Status:** IMPLEMENTED. Landed `2c51766e401`; unit tests `test/01_unit/app/io/run_sdn_lints_profile_spec.spl`, `test/01_unit/compiler/lint/lint_profile_spec.spl`.

## Reserved requirement IDs 015–022

REQ-MC-015 through REQ-MC-022 are reserved for this profile but remain unallocated as of
2026-08-07. The aerospace hardening plan (WP-5) surveyed current gaps and found two
load-bearing issues already covered by REQ-MC-013 and REQ-MC-014 (policy resolution and
project pinning). Future gaps in profile enforcement, policy precedence, or SDK/tooling
integration will claim IDs from this range. No padding requirements were added;
the list contains only verified, specified, landed work.

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

**Status: IMPLEMENTED and LIVE as of 2026-08-07** (this section previously
read "DORMANT pending lint redeploy (WP-3.5)" — that is no longer true and
has been corrected). Verified by positive capability probe: a bare acquire
returned from a fn produces `warning[W-MC-RES-001]` under `bin/simple lint
--profile=critical`, and is correctly silent under `--profile=moderate`.

**Ownership *or* ref count both satisfy this rule.** A refcounted wrapper is
accepted exactly like an affine owning wrapper — measured, and true
incidentally rather than by design: the accept predicate recognises any
`TypeName(...)` constructor and does not inspect which ownership discipline
the wrapper implements. No `*R`/`@R` sigil detection is involved (and none is
possible here — this is a text-level check, and per WP-G `@R`/`-R` erase to
`Infer` even at HIR).

**Blocker on the v2 `deny` promotion — do not promote on this
implementation.** A 245-file sweep yields **208 findings across 78 files**,
overwhelmingly false positives: the check matches an acquire *verb* and never
establishes that the call returns an opaque handle, so it flags
`rt_string_new` (a string value), `rt_array_new` (an array value),
`rt_dir_create` (creates a directory, returns `bool`) and `rt_atomic_int_load`
(an atomic read). The obvious narrowing — requiring a same-prefix paired
release — is **unsound**, silencing genuine resources such as
`rt_io_tcp_socket_create` and `rt_cuda_module_load` whose release lives under
a different prefix; it would trade visible noise for invisible leaks. A sound
rule must key on the declared handle type carried by `@sffi(handle: ...)` /
`resource R`, i.e. a semantic check rather than a text scan. Full measurement,
controls and unsoundness proof:
`doc/08_tracking/bug/w_mc_res_001_overfires_verb_only_heuristic_2026-08-07.md`.
The warn→deny phasing below should be re-evaluated only after that rework.

`W-MC-RES-001` is a landed checker —
`src/compiler/35.semantics/lint/unwrapped_foreign_resource.spl`
(`check_unwrapped_foreign_resource`) — registered in
`src/compiler/90.tools/lint/_LintMain/lint_checks.spl` and
`config_and_model.spl` (allow in moderate/strict/robust, warn in critical,
via the WP-3 canonical policy resolver's `profile_default_levels` — no new
severity table). It is a text-level, intraprocedural, single-assignment
heuristic (documented ceiling in the check's file docstring): it flags a
bare acquire-verb-extern (`rt_..._open`/`_create`/`_new`/`_alloc`, verb
catalog reused from `resource_families.acquire_verbs()`) result that escapes
via `return`, an implicit tail expression, or a direct `self.field`
assignment, without first passing through a wrapping constructor call in the
SAME function; cross-call argument threading and multi-hop variable renaming
are out of scope for v1. Unit-verified over source strings at
`test/01_unit/compiler/lint/unwrapped_foreign_resource_spec.spl` (interpreter
path — the deployed `bin/simple lint` binary predates this source and will
not exercise it until the next lint-binary redeploy, same reachability gap
REQ-MC-012 already documents for this whole family). It additionally depends
on the `resource` declaration (Phase 1, not yet implemented — see
`doc/04_architecture/language/resource/resource_declaration_architecture_2026-08-06.md`)
for the primary wrapped-form example to be checkable as `resource`-typed
rather than only as the hand-written-class fallback. The
`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`
premises table (row 12b: "the enemy is reimplementation, not absence")
applies here too — this WARN-only text heuristic is the checker itself (not
a stand-in ahead of a future semantic checker); a later typed-HIR data-flow
upgrade replaces it in place, it does not get kept alongside it.

## Non-goals / design decisions honored

- Short borrowing range: intended design, not a gap.
- Class-param reference semantics (s19): kept; enforcement layers on via REQ-MC-002.
- Mutable-by-default collections (Decision #3): kept; iterator-liveness restriction only.
- Base (non-MC) profiles keep current ergonomics; this profile is opt-in per package.

## Reserved / proposed requirement IDs (proposed 2026-08-21)

Named-suffix ids reserved by `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`
§14, designed in `doc/05_design/compiler/hardening/critical_completeness_design_2026-08-21.md` and
sequenced in `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md`. All six are
**proposed, not landed**; none consumes the reserved numeric range 015–022.

- `REQ-MC-ANY-001` — unsafe-only `Any`: illegal in safe critical code, legal only inside `unsafe(capabilities: [type_erasure])`, no escape, no direct operators, checked conversion only. (proposed 2026-08-21)
- `REQ-MC-MONO-001` — monomorphic canonical IR: no unresolved type parameter or generic call reaches canonical MIR, no erasure to `Any`, all reachable instantiations in the mono graph and seal. (proposed 2026-08-21)
- `REQ-MC-COMPLETE-001` — static and complete closure: all static variants exhaustively handled, all selected complete variants implement required interfaces, no reachable open `dyn`, no wildcard closes a compiler-IR match. (proposed 2026-08-21)
- `REQ-MC-PIPE-001` — total stage transitions: every producer variant has an explicit `CoverageState`; a missing mapping is a build error; silent fallback replacement is prohibited. (proposed 2026-08-21)
- `REQ-MC-ASPECT-001` — sealed aspect world: all semantics-changing aspects selected before weave, post-weave program rechecked, weave plan part of artifact identity, no late semantic activation. (proposed 2026-08-21)
- `REQ-MC-BOOT-001` — bootstrap and engine parity: seed and self-hosted compiler share one generated feature/coverage manifest; accepted/rejected critical fixture sets match; interpreter/JIT/native semantic differentials are zero on the critical corpus. (proposed 2026-08-21)

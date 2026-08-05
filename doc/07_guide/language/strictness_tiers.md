# Strictness Tiers (Script Modes)

Simple has **two independent classification axes**. Do not conflate them:

| Axis | Controls | Values |
|------|----------|--------|
| **Stdlib memory tier** | runtime / allocation / async model | `nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`, `nogc_async_mut_noalloc` (see `.claude/rules/structure.md`) |
| **Strictness tier** (this guide) | code-quality strictness: which lints fire, at what severity, and whether proof-coverage is gated | `moderate`, `strict`, `robust`, `critical` |

A build target picks one value on **each** axis; they compose freely — e.g. a
`nogc_async_mut_noalloc` baremetal module can be built under `robust`.
Strictness tiers are **not** memory tiers and never change the runtime model.

## The four tiers

| Tier | Audience | Lint behavior |
|------|----------|---------------|
| **moderate** | scripts, prototypes, examples | advisory only — every `deny` default is downgraded to `warn` |
| **strict** | library / reusable code | current defaults (the regression-safe baseline) |
| **robust** | safety-relevant units | Rust-parity level — public-surface + safety/correctness lints elevated to `deny` |
| **critical** | mission-critical systems | robust + REQ-MC rules (`bare_primitive_internal` at `warn`); planned for REQ5+ |

The **robust** and **critical** tiers are part of a **ladder**:
1. strict lint levels (currently run at compile; planned to also run at link),
2. local/internal-primitive-use check surfaced as a WARNING with verified auto-fix (planned),
3. formal-verification **coverage** meta-check — each feature-level public class /
   main-class-of-file *has* a discharged proof (planned; a coverage check, not a prover).

> Rungs 2–3 are on the roadmap. See
> `doc/03_plan/compiler/reliable_mode/reliable_mode_plan.md` for the phased plan.
> Today (P0) the tier selector and per-lint configurability ship for `simple lint`.

## Selecting a tier

Five sources with precedence (**highest to lowest**):
1. `@lint_profile(...)` — file-header attribute (top of file, before defs)
2. `--profile=...` — explicit CLI flag
3. `simple.sdn [lints] profile=...` — project default
4. engine default — `moderate` (interpreter/JIT), `robust` at WARN severity (compiler/loader)
5. legacy baseline — if no tier selected above, behavior is identical to today's defaults

Examples:

```sdn
# simple.sdn — project default
[lints]
profile = "robust"
primitive_api = "deny"   # explicit per-lint override still wins over the tier
```

```bash
simple lint src/foo.spl --profile=robust   # CLI override
```

```simple
@lint_profile(critical)   # file-header attribute (top of file, before defs)

# NOTE: distinct from @profile(critical), the R9 must-use annotation.
```

**Note on compiler/loader defaults:** native builds and module loading use the `robust` tier by default, but all its `deny`-level rules run at `warn` severity during the migration window. Escalation to `error` is a later change, explicitly not yet implemented.

## Deprecated tier aliases (pre-2026-07-28)

The tier names were renamed on 2026-07-28 for clarity. Old spellings still work but emit a one-time deprecation warning per distinct old name:

| Old name | New name |
|----------|----------|
| `lib` | `strict` |
| `reliable` | `robust` |
| `mission-critical` or `mission_critical` | `critical` |
| `moderate` | `moderate` (unchanged) |

Configs using old names continue to work with no behavior change — only the names have changed, not the semantics. Update your configs at your convenience.

## Per-lint configuration

Every lint code now maps to a stable config name, so any lint is governable via
`[lints]` / `@allow(...)` / `@warn(...)` / `@deny(...)`. Newly-configurable
families include: `unused_code` (W001-3), `style_convention` (ST001-3),
`unsafe_pattern` (S001-3), `concurrency_misuse` (CC001-2), `closure_capture`
(CLOS001), `ignored_return` (RET001), `multiline_bool` (BOOL001),
`memory_safety` (SAFE001/3), `visibility_boundary` (W0401-3),
`database_integrity` (D001), `tracking_traceability` (TRK001).

## Relationship to the rejected "High-robustness mode"

The `robust` and `critical` tiers supersede the previously-rejected "High-robustness mode"
(`simple_language_comparison.md`). Instead of an unprovable blanket guarantee, they
realize the configurable strict-lint + `@deny(non_exhaustive_match)` + proof-coverage
approach that document prescribed — dialed by context, not asserted. `critical` adds
mission-critical safeguards like bare-primitive-internal tracking.

## Runtime match-exhaustiveness diagnostics (`SIMPLE_SAFETY_PROFILE`)

**Distinct from the lint-`profile` axis above.** The `[lints] profile=...` /
`@lint_profile(...)` / `--profile=` selectors above are a **compile-time lint**
severity axis for `simple lint`. `SIMPLE_SAFETY_PROFILE` is a separate,
dedicated **runtime** env-var axis (see
`src/compiler/80.driver/driver_safety_severity.spl`), read at pure-Simple
interpreter start (`eval_init()` in
`src/compiler/10.frontend/core/interpreter/eval_decls.spl`) to decide the
severity of two `match`/enum diagnostics. It shares vocabulary with the lint
axis (`critical`, and the frozen `mission-critical`/`mission_critical` alias)
but is evaluated independently — setting `--profile=critical` for `simple
lint` does **not**, by itself, change `SIMPLE_SAFETY_PROFILE`-gated runtime
behavior, and vice versa.

**Why runtime, not compile-time.** A `match` on an enum is diagnosed for
exhaustiveness at RUNTIME, not compile-time, and deliberately so: a
compile-time checker would have to resolve which `enum` declaration a bare
arm name (`case Style:`) belongs to, through the same global bare-name
registry used everywhere else in the compiler. That registry is **not**
sound for this purpose — as of the measurement in
`doc/08_tracking/bug/match_enum_fallthrough_silent_2026-08-01.md`, 336-421+ of
the ~1,410-1,590 enum names declared in-tree are declared more than once, so a
compile-time checker built on that registry inspects the *wrong* enum at a
large fraction of candidate sites (both missing real collisions and firing on
false ones). The runtime diagnostics below instead read the scrutinee's
*actually resolved* enum value and variant off the value itself
(`val_enum_variant_name`), which carries no such ambiguity. **Do not
"fix" this into a compile-time check without first reading that bug doc** — a
prior compile-time attempt at the same idea (`src/compiler/35.semantics/lint/match_exhaustiveness.spl`,
`src/compiler/70.backend/backend/exhaustiveness_validator.spl`,
`src/compiler/95.interp/interpreter/pattern.spl`) is dead code, uncalled,
precisely because of this.

Two independent diagnostics, both interpreter-tier, both landed in
`src/compiler/10.frontend/core/interpreter/eval_tables.spl` and wired from
`SIMPLE_SAFETY_PROFILE` in `eval_decls.spl`'s `eval_init()`:

| Diagnostic | Fires when | Default severity | `critical`/`mission-critical` severity |
|---|---|---|---|
| **Fall-through** (`report_match_fallthrough`) | a `match` on an enum takes **no** arm at all (no wildcard, nothing matched) | warning (unchanged from today) | **hard error** — `eval_set_error` halts interpreter-tier execution at the `match` (`match_fallthrough_set_abort`) |
| **Wildcard-catch** (`report_match_wildcard_catch`) | a wildcard/bare-binder arm (`case _:`, a bare lowercase binder such as `other:`, `_ => expr`) is the arm that actually fired on an enum value | **no diagnostic at all** (off by default — a real arm DID fire) | **warning** (`match_wildcard_catch_set_enabled`) — no abort variant exists for this one yet |

The wildcard-catch diagnostic exists because a catch-all arm silently absorbs
*any* variant, including ones added to the enum after the match was written —
for mission-critical code that defeats exhaustiveness the same way a missing
arm does, just discovered later (when a new variant is added, not when the
match was written). It is sound for the same reason the fall-through
diagnostic is: which *pattern* is a wildcard is decided from that arm's own
AST shape (`pattern_is_wildcard_catch` in `eval.spl`), not from a bare-name
"which enum declares this variant" lookup.

```bash
SIMPLE_SAFETY_PROFILE=critical bin/simple run program.spl   # both diagnostics at Deny severity
SIMPLE_SAFETY_PROFILE=robust   bin/simple run program.spl   # Warn severity — same as unset today
```

**Deferred compile-time promotion.** A companion, non-fatal diagnostic exists
at MIR enum-match lowering (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`,
no-default path) for the compiled/JIT lanes; it is deliberately kept off the
`_mir_error_is_fatal` allowlist (`src/compiler/80.driver/driver_pipeline_lowering.spl:119`).
Promoting it to a hard compile error (see the `# TODO:` at that call site) is
blocked on the same duplicate-enum-name problem above and is explicitly future
work — do not attempt it without a collision-aware resolver first.

See also: `doc/glossary.md` ("Strictness Tiers"), `strictness_tiers_tldr.md`,
`doc/08_tracking/bug/match_enum_fallthrough_silent_2026-08-01.md`.

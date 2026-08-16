# Seed HIR lowering: the builtin-`Option` exception is keyed on a NAME, so a user-declared `enum Option` is misrouted

**Status:** open
**Found:** 2026-08-16, structural review of `8d96687c991` on `origin/main`
**Severity:** high — silently reintroduces an irrefutable-pattern bug that a prior fix was written to close
**Component:** Rust seed, `hir/lower` (both the expression and statement match-lowering twins)

## Summary

Commit `8d96687c991` ("fix(seed): match builtin Option None in HIR lowering") added an exception so
that the builtin `Option<T>` — which registers as a `HirType::Enum` named `"Option"` but whose runtime
representation is nil-boxing — takes the optional-shaped fast paths instead of the enum-discriminant
path. The fix is correct for the builtin. But it identifies the builtin by **name string**, while the
runtime identifies it by **reserved enum id**. A *user-declared* `enum Option` matches the name test
and gets misrouted onto the nil-boxing path, where its patterns become irrefutable.

This is not a hypothetical collision: the shape is declared in-tree, in the very regression test the
earlier fix exists to satisfy.

## The mismatch

The new predicate, identical in `hir/lower/expr/control.rs` and `hir/lower/stmt_lowering.rs`:

```rust
let subject_is_builtin_option = matches!(
    self.module.types.get(subject_ty),
    Some(HirType::Enum { name, variants, .. })
        if name == "Option"
            && variants.len() == 2
            && variants.iter().any(|(n, p)| n == "Some" && p.is_some())
            && variants.iter().any(|(n, p)| n == "None" && p.is_none())
);
let subject_enum_owns_variant = !subject_is_builtin_option && matches!(/* … */);
```

Both runtimes gate the enum half of the check on a **reserved id**, never on the name:

- `src/compiler_rust/runtime/src/value/objects.rs:490` — `rt_is_none` is true for nil, or for
  `enum_id == OPTION_ENUM_ID` (reserved id 1) with `discriminant == hash("None")`.
  `rt_is_some` (`:505`) is exactly `!rt_is_none(value)`.
- `src/runtime/simple_core/core_values.spl:61` — the pure-Simple twin: `if rt_enum_id(value) != 1: return 0`.

A user-declared `enum Option` is allocated an ordinary enum id. It is never id 1.

## Failure mode

For a user-declared `enum Option: Some(i64); None`, `subject_is_builtin_option` is true, so
`subject_enum_owns_variant` is false and lowering takes the early returns at
`hir/lower/expr/control.rs:625-643`:

- `case Option::Some(v)` → `rt_is_some(obj)` → `!rt_is_none(obj)`. The object is not nil and its
  `enum_id != 1`, so `rt_is_none` is false and **`rt_is_some` is always true — the arm is
  irrefutable**. Worse, the early `return` fires before `nested_payload_condition` further down, so
  the payload sub-pattern binding `v` is **discarded outright**.
- `case Option::None` → `rt_is_none(obj)` → `enum_id != 1` → **always false; the arm never matches.**

That is verbatim the failure the pre-existing comment in `stmt_lowering.rs` records as the reason
`subject_enum_owns_variant` was introduced in the first place — *"which made `case Some(x)`
irrefutable and bound x = 3"*. The new exception re-opens it for any enum named `Option` of that shape.

## Reachable in-tree

- `src/compiler_rust/driver/tests/runner_tests.rs:851,870` — `runner_handles_option_type` declares
  exactly `enum Option: Some(i64); None` and asserts `42` then `99`. The `99` case
  (`let x = Option::None`) is tested against the `Some(v)` arm first, which is now irrefutable.
- `src/compiler_rust/driver/tests/runner_tests.rs:892` — `runner_handles_option_type_functions`, same shape.
- `src/compiler/30.types/bidirectional_types.spl:105` — the self-hosted compiler's own type system
  declares `enum Option<T>`.
- `src/compiler_rust/lib/std/src/core/option.spl:4` — stdlib `enum Option<T>`; here the misrouting is
  presumably intended, since this declaration *is* the builtin, but it is matched by the same name
  test rather than by identity, so the intent is not expressed.

## Suggested direction (not applied)

Key the predicate on the same identity the runtime uses — the reserved `OPTION_ENUM_ID` — rather than
on `name == "Option"`, so compile-time and runtime agree on what "builtin Option" means. If the
`TypeId`/`HirType` layer does not carry the reserved id at that point, the id should be threaded to
where the decision is made; matching on a user-ownable name string cannot be made correct, because a
user enum is allowed to have that name and that shape.

Secondary, from the same review: the ~14-line predicate is duplicated verbatim across the two twins,
held in sync only by a comment. Whatever the fix, it wants to be one shared helper — the duplication
is what will let the two drift.

## Companion defect found while authoring the fence: the LINTER also dies on a user `Option`

A user-declared `enum Option` is under-handled in more than one place. This
six-line file is enough to make `simple lint` fail:

```
enum Option:
    Some(i64)
    None

fn main() -> i32:
    return 0
```

```
$ simple lint opt_only.spl
error: semantic: method 'with_fix' not found on value of type object in nested call context
$ echo $?
1
```

The full lane fixture (`test/fixtures/user_option_enum_match/main.spl`) fails
the same way, reporting `with_easy_fix` instead of `with_fix` — the same
diagnostic-builder chain, one link further along. Control: an otherwise
identical file with the enum removed lints clean (`Lint passed: all files
clean`), and a file exercising `.to_text()` alone also lints clean, so the enum
declaration is the trigger and nothing else in the fixture is.

The shape of the message says the linter is **constructing a diagnostic** and the
fix-builder call fails on an untyped receiver — valid source, exit 1, no usable
diagnostic.

**Scope correction — this is NOT specific to `Option`.** A wider control run
shows the same crash on files that contain no `enum Option` at all, including a
pre-existing spec this lane never touched:

| File | Verdict |
|---|---|
| `opt_only.spl` (6 lines, user `enum Option`) | FAIL `with_fix` |
| `totext_only.spl` (3 lines, no enum) | pass |
| `test/fixtures/engine2d_font_offload_fallback/main.spl` | pass |
| `test/03_system/qualified_pure_simple_runtime.spl` | pass |
| `test/03_system/.../engine2d_font_offload_fallback_system_spec.spl` (new) | FAIL `with_easy_fix` |
| `test/03_system/.../user_option_enum_match_lowering_system_spec.spl` (new) | FAIL `with_easy_fix` |
| `test/03_system/feature/web_platform/html/kbd_samp_var_rendering_spec.spl` (**pre-existing, untouched**) | FAIL `with_fix` |

So the correct statement is: **`simple lint` has a general diagnostic-builder
defect** (`with_fix` / `with_easy_fix` not found on an untyped receiver) with at
least two independent triggers — one reachable from a six-line user `enum
Option`, and another that fires on system specs generally, including ones that
predate this lane. The `Option` repro is genuine and minimal, but it is one
entry point into a broader defect, not an `Option`-specific bug. The
pre-existing-spec row is the load-bearing control: it proves the crash is not
introduced by the files added here.

**Provenance limit, stated plainly:** observed with the Rust seed's linter,
because no pure-Simple linter exists to cross-check it —
`bootstrap/stage3/simple` exposes only `compile` and `native-build`, and
`bootstrap/stage3/simple lint` is `unknown command`. Recorded as a reproducible
tool defect, **not** as evidence for any acceptance criterion in this lane.
Whether the self-hosted linter shares the defect is unverified.

## Evidence and limits

Source trace only. No test was executed: this lane's evidence rule requires pure-Simple self-hosted
execution and forbids Rust seed test results, and in any case no working self-hosted binary exists on
this machine — see
`stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`, which records a
fleet-wide sweep finding all five self-hosted artifacts non-functional. The claim here rests on
reading the lowering predicate, the two early-return branches it selects, and both runtime
implementations of `rt_is_none`/`rt_is_some`; each is cited by file and line above. **Running
`runner_handles_option_type` against a rebuilt seed would confirm or refute it in one step** and is
the recommended next action for whoever owns the seed.

## Rust seed: FIXED 2026-08-16 (compiles clean, not yet run)

Both sites now additionally require the subject enum to be GENERIC, which is the
property that actually separates the two cases:

- the builtin is registered by `instantiate_builtin_generic_enum`
  (`hir/lower/type_resolver.rs:104-110`) with `generic_params: vec!["T"]`;
- a user-declared `enum Option: Some(i64) / None` clones its own declaration's
  `generic_params`, which is empty (`hir/lower/type_registration.rs`,
  `import_loader.rs` — every user path uses `enum_def.generic_params.clone()`).

```rust
Some(HirType::Enum { name, variants, generic_params, .. })
    if name == "Option"
        && !generic_params.is_empty()      // <-- added
        && variants.len() == 2
        ...
```

Applied to `hir/lower/expr/control.rs:609` and `hir/lower/stmt_lowering.rs:2310`,
which the code comments require be kept in sync. `cargo check --release --bin
simple` passes.

**Not verified at runtime.** A seed binary cannot currently be linked at all —
see `doc/08_tracking/bug/rust_seed_link_fails_duplicate_rt_heap_symbols_2026-08-16.md`.

**Residual limit, stated rather than hidden:** a user who declares a GENERIC
`enum Option<T>: Some(T) / None` still collides. Distinguishing that case needs a
provenance flag on `HirType::Enum` set by `instantiate_builtin_generic_enum`,
which is a wider change than this lane covers.

## Pure-Simple compiler: SAME DEFECT CLASS, unfixed

The self-hosted compiler keys the same lane on the bare name, at three MIR sites
in `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`:

| Line | Code | Effect on a user-declared `enum Option` |
|---|---|---|
| 2281 | `var option_flat_lane = enum_name == "Option"` | routes it through the Option flat-lane discriminant normalization |
| 3196 | `if enum_name == "Option": self.option_value_locals[tagged.id] = true` | marks an ordinary enum local as an option value |
| 3307 | same, MethodCall construction path | same |

Notably that file's own `enum_bare_of` docstring (line 101-110) already warns that
comparing a resolved owner "against a bare literal (`== \"Option\"`)" silently
takes the wrong branch — the warning is about qualified-vs-bare names, but the
user-shadowing case is the same failure mode and is not guarded.

Not fixed here: it cannot be verified — no functional self-hosted binary exists
(fleet sweep, 1099 instances, 19 unique, all five self-hosted artifacts
non-functional). The dual-toolchain SSpec
(`test/03_system/compiler/user_option_enum_match_lowering_system_spec.spl`) runs
the same fixture under BOTH compilers and names whichever one disagrees, so this
is fenced the moment either toolchain works.

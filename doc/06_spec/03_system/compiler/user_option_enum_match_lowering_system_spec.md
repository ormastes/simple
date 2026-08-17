# User-declared `Option` enum match lowering (system lane)

**Category:** Language
**Status:** In Progress — fail-closed, blocked on a qualified pure-Simple runtime
**Source spec:** `test/03_system/compiler/user_option_enum_match_lowering_system_spec.spl`
**Requirements:** REQ-OPTLOWER-001, REQ-OPTLOWER-002, REQ-OPTLOWER-003

## Purpose and Audience

Fences a regression class in match lowering: a **user-declared** enum named
`Option` must be lowered on the enum-discriminant path, not on the nil-boxing
fast path reserved for the builtin `Option<T>`.

Audience: anyone editing the match-lowering twins in
`hir/lower/expr/control.rs` and `hir/lower/stmt_lowering.rs`, or their
self-hosted equivalents.

## Scope and Preconditions

Requires an admitted pure-Simple runtime (`SIMPLE_QUALIFIED_RUNTIME`); the Rust
bootstrap seed is not acceptable evidence for this lane. Without one these
scenarios fail rather than skip.

This must be a **native** lane. The tree-walk interpreter binds match arms from
`HirFunction` directly and cannot observe the defect, so an interpreted run
would report green against a broken compiler.

## Primary Workflow

| Step | Action |
|------|--------|
| 1 | Admit a pure-Simple runtime and native-build the user-`Option` probe |
| 2 | Execute the probe |
| 3 | Assert both arms of a user-declared `Option` behave as declared |

## Key Concepts

| Concept | Description |
|---------|-------------|
| Builtin `Option<T>` | Nil-boxed at runtime; identified by a **reserved enum id** (1) |
| User `Option` | An ordinary enum object with an ordinary id, that merely shares the name |
| Misroute | Treating the latter as the former makes `Some` irrefutable and `None` unmatchable |

## Scenarios

### Binds the payload of a user-declared Some arm — REQ-OPTLOWER-001

`Option::Some(42)` reaches the `Some` arm **and** binds `42`. Under the misroute
the early return fires before payload handling, so the binding is dropped.

### Matches a user-declared None arm — REQ-OPTLOWER-002

`Option::None` reaches its own arm and yields `99`. Under the misroute
`rt_is_none` checks `enum_id == 1`, is false for a user enum, and the arm never
matches.

### Keeps the Some arm refutable against a None value — REQ-OPTLOWER-003

Matching a `None` value against a `Some(v)` arm must not match. Under the
misroute `rt_is_some` is `!rt_is_none`, which is unconditionally true for any
non-nil enum object, making the arm irrefutable.

## Related Specifications

- `doc/08_tracking/bug/seed_builtin_option_name_heuristic_breaks_user_option_enum_2026-08-16.md` — the traced defect this lane fences

## Evidence and Provenance

Derived from a source trace of `8d96687c991`, which keys its builtin-`Option`
exception on `name == "Option"` while both runtimes key on the reserved enum id
(`src/compiler_rust/runtime/src/value/objects.rs:490`,
`src/runtime/simple_core/core_values.spl:61`).

**No runtime evidence has been produced**: no qualified pure-Simple runtime
exists on the reference machine as of 2026-08-16.

## Recovery and Troubleshooting

| Observation | Meaning |
|---|---|
| `none_arm` returns `42` | The misroute itself — the `Some` arm captured a `None` value |
| `none_via_some` reports `some-matched-none:*` | Same misroute, observed directly |
| `no qualified pure-Simple runtime admitted` | Toolchain blocker, not a lowering defect |

## Compatibility and Limitations

Covers the two-variant `Some(payload)`/`None` shape only — the exact shape the
name heuristic collides with. Says nothing about generic `Option<T>` inference
or about `Result`.

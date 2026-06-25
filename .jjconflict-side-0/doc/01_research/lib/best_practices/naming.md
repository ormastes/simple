# Naming

Status: production API contract.

This document defines the naming rules for public Simple APIs. The goal is a
Ruby-like surface that stays short, readable, and predictable without hiding
allocation, mutation, blocking I/O, or failure.

## Principles

- Prefer the shortest name that still exposes the operation: `map`, `select`,
  `reject`, `each`, `join`, `split`, `fetch`.
- Prefer one canonical verb per operation. Aliases are allowed only when they
  improve common-use ergonomics and forward to the canonical implementation.
- Names must reveal side effects:
  - Mutating methods end with `_in_place` unless the receiver type is explicitly
    a builder, stream, session, handle, cursor, or buffer.
  - Blocking operations include `blocking_` when an async alternative exists.
  - Fallible operations return `Result<T, E>` and use verbs like `parse`,
    `open`, `read`, `decode`, or `compile`; they do not hide failure behind
    nullable returns.
- Avoid type noise in method names. Prefer `array.map(fn)` over
  `array.map_array(fn)` and `path.read_text()` over `read_file_to_string(path)`.
- Use consistent conversion prefixes:
  - `to_*`: allocate or produce a new value.
  - `as_*`: cheap borrowed or view-like access.
  - `into_*`: consume or transfer ownership.
  - `try_*`: fallible fast-path or optional operation where failure is expected.
- Predicates should read naturally and use the language predicate form where
  available. Prefer `empty.?`, `valid.?`, `present.?` over `is_empty` for new
  public APIs.

## Canonical Verb Families

| Operation | Preferred names | Avoid |
| --- | --- | --- |
| Iterate for side effects | `each` | `for_each_item`, `iterate_all` |
| Transform | `map` | `transform_values` when receiver already implies values |
| Filter keep | `select` | `filter_true`, `where_all` |
| Filter drop | `reject` | `filter_not` |
| Find one | `find`, `find_index` | `search_for_one` |
| Require key/index | `fetch` | `get_or_fail` |
| Optional key/index | `get`, `at` | `maybe_get_value` |
| Append one | `push`, `append` | `add_item_to_end` |
| Append many | `extend`, `concat` | `append_all_items` |
| String conversion | `to_string`, `as_str` | `stringify`, `str_value` |
| Parsing | `parse`, `try_parse` | `from_string_maybe` |
| Validation | `validate`, `check` | `do_validation` |

## Alias Policy

Ruby-inspired aliases may exist when they meet all of these rules:

1. The alias is common enough to reduce real call-site noise.
2. The alias forwards to one canonical implementation.
3. The docs name the canonical method.
4. Tests cover the canonical behavior, not duplicated alias internals.

Allowed examples: `each -> iter`, `select -> filter`, `reject`, `fetch`,
`empty.?`, `present.?`.

Rejected examples: aliases that only change word order, duplicate behavior, or
hide different failure semantics.

## Predicate Migration Gate

The current codebase still contains legacy `is_` and `has_` helper names. They
are advisory debt, not immediate breakage, because removing them without aliases
would break established callers. New public-ish APIs must not increase that
debt.

The enforcement baseline lives in
`scripts/audit/api_consistency_baseline.json`, and
`scripts/audit/api_consistency_audit.spl` fails if the total or per-root
predicate-prefix count grows. Lower the baseline only after adding the preferred
predicate API, migrating callers, keeping any needed compatibility alias, and
updating tests.

## Error and Warning Names

Diagnostic constructors must name the user-visible problem, not the compiler
phase: `missing_field`, `unknown_method`, `invalid_import`, `type_mismatch`.
Internal phase names belong in trace metadata, not in the primary public API.

Diagnostic fields should use the same names across compiler, LSP, CLI, and MCP:
`code`, `severity`, `message`, `path`, `line`, `column`, `span`, `hint`,
`related`, `fixes`.

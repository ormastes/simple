# Dev ids — making an in-development workstream addressable by name

Status: landed 2026-08-23.
Builds on: `doc/05_design/app/testing/in_development_tag.md`.

## Problem

`# @tag:in-development` marks a spec as work-in-progress: it still EXECUTES,
its verdict is neutralised in a sweep, and an unexpected pass is reported as
ready to promote. What it does not do is say *whose* work-in-progress it is.
With three sweep lanes mass-tagging the tree at once, `simple tags --tag
in-development` returns everybody's WIP, so an active dev session has no way
to run exactly its own set.

## Syntax chosen: `# @tag:dev-id-<id>`

A spec belonging to a named workstream carries a second ordinary tag beside
the in-development tag:

```
# @tag: in-development, dev-id-auth-rework
```

The id is everything after the reserved `dev-id-` prefix, folded through
`tag_normalize` (lowercase, `_` → `-`) exactly like every other tag.

**Why this shape: it required zero grammar change to either extractor.**
That was the deciding evidence, gathered before writing any code:

- `std.test_runner.test_manifest_scanner.extract_tags` already splits a
  `@tag:` directive on commas (`test_manifest_scanner.spl:277`), so a second
  tag on that line is already a first-class tag today.
- `std.spec.in_development.spec_tags` scans `@tag:` followed by
  `[A-Za-z0-9_-]+` (`in_development.spl:_is_tag_char`). `-` is already a tag
  character, so `dev-id-auth-rework` is already a legal tag name.

Consequently `bin/simple tags --tag dev-id-auth-rework` selected exactly the
right set on the day the module landed, before any consumer existed — the
practical test of a design that reuses a channel rather than adding one. It
is also the only option that is automatically visible to the Rust runner's
existing `--tag` (`src/compiler_rust/driver/src/cli/test_runner/args.rs:24`).

### Alternatives rejected

| Option | Why rejected |
|---|---|
| `# @dev:<id>`, a second directive | A second parser. `extract_directive_lines` needs a new branch, `spec_tags` needs another, and the Rust runner's `--tag` would not see it at all — a dev id would be invisible to the one engine that already has tag filtering. |
| `@tag:in-development(auth-rework)` | `(` and `)` are not tag characters in either extractor. This is a grammar change to the SHARED channel: all 1,022 existing uses and both engines would have to agree at once, to buy a nesting a sibling tag already expresses. |
| `@tag:in-development/auth-rework` | Same objection, plus adding `/` to the tag charset changes what every unrelated tag means. |
| `@tag:in-development-auth-rework` | Needs no grammar change, but breaks the documented EXACT-name match: such a spec stops being in-development at all (`in-development-notes` deliberately does not answer for `in-development`), so it would need both tags anyway — i.e. this design, minus the readable prefix. |

## Selection semantics, and how they square with the landed rule

The landed rule is that a tagged spec **still executes** and it is only the
VERDICT that is neutralised. Dev ids do not touch that. `dev_selection_includes`
decides execution only; `classify_in_development` still decides the verdict.

| mode | flag | executes |
|---|---|---|
| `Default` | *(none)* | everything, in-development **included** |
| `Only` | `--in-development` | only in-development specs |
| `OnlyId` | `--in-development=<id>` | only in-development specs with that id |
| `Exclude` | `--no-in-development` | everything except in-development specs |

Default-include is what the user asked for and what the landed semantics
already imply. `--no-in-development` is the only mode that stops a tagged
spec running, and it is opt-in — so nothing silently loses the
unexpected-pass promotion signal that whole-suite execution exists to
produce.

An in-development spec carrying **no** dev id is reported as its own
category (`tag_index_unnamed_in_development`), never hidden: it is reachable
by no id-scoped run, and an invisible backlog is the exact failure this
surface exists to prevent. A `dev-id-` tag on a spec that is *not*
in-development is not counted, so a promoted spec stops inflating the
workstream it has left.

## Engine independence

The run set is produced by `bin/simple tags ... --paths` (bare
newline-separated paths) and composed with `$( )`:

```
bin/simple tags --dev-ids                                     # what exists
bin/simple test $(bin/simple tags --dev-id auth-rework --paths)
bin/simple test $(bin/simple tags --in-development --paths)
bin/simple test $(bin/simple tags --no-in-development --paths)
```

This has no engine-specific half at all, which is the point: a filter flag
implemented in one runner only is a trap, and that is exactly why `tags` was
made a top-level command in the first place.

## Deliberately deferred

Wiring `--in-development[=<id>]` / `--no-in-development` as native flags on
`bin/simple test` requires editing `src/app/test_runner_new/**`, which is
owned by the in-development-tag runner lane and is being edited concurrently.
The rule is already implemented as a single shared predicate
(`dev_selection_includes`), so that lane can adopt it in one call rather than
re-deriving it. Until then the `--paths` composition above is the supported
route, and it works on both engines today.

## Files

| Path | Role |
|---|---|
| `src/lib/nogc_sync_mut/tag_query/dev_id.spl` | Pure id parsing, selection predicate, index queries |
| `src/app/tag_query/main.spl` | `--dev-ids`, `--dev-id`, `--in-development[=<id>]`, `--no-in-development`, `--paths` |
| `test/01_unit/lib/tag_query/dev_id_spec.spl` | 21 scenarios; ERRORs pre-fix, 21/21 post-fix |

## Incidental finding (not fixed here)

`x[expr:]` — an open-ended slice with a computed start — trips the compiler's
"Common mistake detected: Use `<>` instead of `[]` for generics" heuristic as
a false positive. It is a warning, not an error, and the code ran correctly;
`.slice(a, b)` is used instead to keep the surface warning-free. Recorded
rather than silently normalised.

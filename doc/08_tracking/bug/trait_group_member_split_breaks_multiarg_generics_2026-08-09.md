# `parse_trait_group_members` splits on `,` naively — multi-arg generic members break

**Status:** FIXED (2026-08-09) — see commit 40d36dceba0289b112cb166a90da64786a953dc2, which added split_top_level_commas() and a regression spec in test/01_unit/app/desugar/trait_group_spec.spl.
**Found:** 2026-08-09, during P0 (trait `with` groups + `.from()` sugar, landed as `50f06dcdd56`)
**Severity:** low today, latent — no current caller hits it
**Component:** `src/app/desugar/trait_scanner.spl` (`parse_trait_group_members`)

## Defect

`parse_trait_group_members` splits a trait-group header's member list on a bare
`,`. A member carrying a generic with more than one argument therefore splits at
the argument comma instead of the member boundary:

```simple
trait Store with Reader<K, V>, Writer:
```

splits to `Reader<K`, `V>`, `Writer` — three bogus members instead of two real
ones.

## Why it is not currently observable

The Rust parser handles this correctly: `parse_trait()` reuses `parse_type()`,
which parses generic arguments properly and yields `Vec<Type>` for
`super_traits`. Only the **desugar lane's** re-parse of the header text is
naive. The one production consumer today (`DebugProfiler with DebugTarget,
ProfileTarget`) has no generic members, so nothing fails yet.

This is the two-implementations hazard: the same grammar is parsed twice, in two
languages, with two different levels of rigor. The Rust side is right; the
Simple side is a shortcut that will diverge the moment a generic member appears.

## Fix

Split on top-level commas only — track `<`/`>` depth (and `(`/`)` for
completeness) and break only at depth 0. The same helper is worth reusing for
any other comma-separated type list the desugar lane re-parses.

## Reproduction / oracle

No spec covers it — that absence is part of the defect. A negative fixture in
`test/01_unit/app/desugar/trait_group_spec.spl` declaring
`trait Store with Reader<K, V>, Writer:` and asserting exactly two members named
`Reader<K, V>` and `Writer` fails today and passes after the fix.

## Related

- `doc/02_requirements/language/trait_group_with_clause.md` — feature request
- `src/compiler_rust/parser/src/types_def/trait_impl_parsing.rs` — the correct
  parse, for reference

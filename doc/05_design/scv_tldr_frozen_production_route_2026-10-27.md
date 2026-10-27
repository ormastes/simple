# Frozen TLDR production caller: first integration slice

Date: 2026-10-27. Source implementation and authored tests; runtime qualification
pending. Owner: `/root/impl_tldr_route`. Base:
`25cdeee5d5da8f8c7c3ab530d43bc2fd4a360d26`, target `release/1.0.0`.

This slice implements the compiler boundary from
[the approved phase 2 design](scv_full_phase2_2026-10-27.md). It does not complete
the full SCV/phase 2 plan or admit a compiler runtime.

## Production path and ownership

`CompilerDriver.stage_parse` calls `parse_all_committing_impl`, whose shared
phase gate selects streaming surfaces for `CompileMode.Check` when the existing
default-off `SIMPLE_TLDR_IMPORTS=1` switch is enabled. The same gate controls
orchestration carrier reporting, reclamation, and subsequent HIR lowering.
The flag has one leaf memo owner; changing the environment does not change the
process decision until the existing test reset API is called.

After phase 1 freezes source owners, phase 2 calls
`tldr_route_frozen_inputs_v1(paths, modules, contents, claimed)`. Every import
must name a module in this exact declared inventory. There is no filesystem
resolver, recursive closure discovery, or live source fallback. Ordinary Check
claims the full inventory. An existing HIR-worker static slice claims its own
files and requests interface projections for unclaimed inventory members.

The existing `add_streaming_module_surface` parser receives an explicit frozen
parse-text override. Its `SourceFile` retains original frozen bytes, physical
path, source index, and module identity. Consequently the original source SHA
and surface content identity remain authoritative. The selected frontend and
environment variant policy still own parsing; target/configuration are not
reconstructed from summary text. Existing summary syntax and surface schema
are unchanged. Surface registry finalization and retention use the existing
production owner, followed by normal HIR lowering.

Summary convertibility admits an interface, but the sorted summary source is
not its source-coordinate map. Production parses the existing source-order
skeleton after an exact-width adapter preserves every unchanged header,
comment and import, each original line's byte width, and LF/CRLF separators.
Eligible erased blocks contain one inert `0` expression and same-width spaces.
ASCII is the explicitly supported byte domain; Unicode falls back unchanged.

The parser's `parse_fn_decl` records `decl_start` before consuming `fn`, calls
`parse_block`, then records `lex_token_start_get()` as the declaration end
(`core/_ParserDecls/fn_struct_decls.spl`). The indented block parser consumes
DEDENT with `parser_advance()` before returning (`core/parser_stmts.spl`). Thus
the function end belongs to the following token/EOF, whose offset is preserved
by exact-width projection, rather than the erased body's final expression.
The bridge copies that declaration span into function and parameter headers.
No posthoc guessed/reordered span mapping is applied. Runtime confirmation of
this code-level argument remains pending.

Projected parses use the existing uncached selected frontend. An interface
projection must not populate a full-source phase 2 parse artifact or an
objectless declaration proof. A separate admitted projection-cache authority
would be required before enabling that cache optimization. No package action
key semantics, frontend SHA schema, or TaskRunner API changes in this slice.

## Conservative boundaries

Missing/duplicate module identities, duplicate paths, legacy/relative imports
outside the exact universe, global advice, and macro scopes refuse explicitly.
Full-inventory target receipt mode refuses because its exact parse-source
receipt cannot describe projected text. Parse-cache shards, native MIR and
file-worker body consumers refuse rather than consuming missing bodies.
Coverage, MC/DC and VHDL retain explicit streaming rejection. Phase 1 entry
closure guards and both legacy worker closure guards remain in force.

Any attribute, including module-wide `@no_gc(strict)` and `@layer` before
imports, uses exact frozen-source fallback until summary authority includes
those facts. Nested declaration forms also retain frozen source. Unsupported
summary rows, inferred return types, and trait/impl/generic/type-alias/constant
contracts fall back to parsing that module's frozen bytes. No fallback opens
its path. This may parse more than the claimed files and is counted. Interface
projection parsing also runs a parser: this slice makes no zero-parser claim.
Dynamic HIR claim queues refuse because their eventual claims are not frozen.
Static HIR slices use the existing shard claim predicate; this route creates
no process-global claim/HIR restriction state. Actual source/interface parse
counters belong to each driver, and a distinct-context consecutive regression
checks that later requests neither inherit the slice nor overwrite counters.
Concurrent frontend execution is not newly qualified: the inherited parser
and diagnostic globals still require the compiler's existing execution model.

## Authored oracle and pending evidence

`test/01_unit/compiler/driver/tldr_frozen_production_route_spec.spl` exercises
the production `stage_parse` caller, compares a cold full-source registry with
the routed registry, and edits every live source after phase 1 admission.
Its oracle checks four semantic hash limbs, callable names, resolved import
targets, canonical identity, content identity, and original source SHA.
It compares `nogc_strict`, module layer tags/DAG facts, and every span field on
functions, parameters and parameter/return types. Span fixtures cover leading
comments, z-then-a declaration order, multiline bodies, trailing comments,
CRLF and a one-byte body at EOF; Unicode must fall back byte-for-byte. The
production fixture still requires one actual interface projection alongside
the module-attribute fallback, so fallback cannot masquerade as route success.
It asserts actual source/interface parse calls, the existing compiler parser
scheduling counter, and `flat_parse_module_body_calls` deltas. Separate cases
cover refused universes, unsupported lanes, advice, and frozen-only fallback.
The prior TLDR route spec now expects undeclared imports to stop at phase 2
and exercises the complete-inventory Check caller without injected surfaces.

No runtime, tests, checker, smoke checks, or docgen were executed: the parent
session found no admitted self-hosted Linux binary and prohibited seed fallback.
After admission, run once with the admitted runtime:

```text
<runtime> test test/01_unit/compiler/driver/tldr_frozen_production_route_spec.spl --mode=interpreter
<runtime> test test/01_unit/compiler/driver/tldr_route_spec.spl --mode=interpreter
<runtime> test test/01_unit/compiler/driver/worker_surface_differential_spec.spl --mode=interpreter
```

Compiler/core runtime and MCP native smoke checks, generated-manual review,
coverage, configuration variants, and native semantic/latency/RSS evidence
remain pending. The existing parser owner was 1599 lines at the base and needs
a dedicated semantics-preserving split; the present change adds narrow hooks
and does not claim compliance with the 800-line owner limit. This is not a
verify PASS or release authorization.

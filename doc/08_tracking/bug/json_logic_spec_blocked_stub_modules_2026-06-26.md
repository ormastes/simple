# Bug: json_logic_spec blocked by stub-only json sub-modules

## Re-opened and re-fixed 2026-11-25 — seed privacy enforcement rejected the spec's imports; API fns marked `pub`

The 2026-09-13 closure below claimed the spec's eight imports "all resolve and
run". On the current tracked seed (`bin/simple.exe`, Rust seed v1.0.0-rc.1)
that no longer holds: the seed's privacy check rejects CALLS to plain-`fn`
names imported from outside the module, so the spec's import list loads but
every call to `json_minify`, `json_beautify`, `json_diff`, `json_patch`,
`json_unflatten_object`, `json_deep_equals`, `jsonl_is_valid`, and
`jsonl_content_is_valid` fails semantic with
`private fn ... is not visible ... mark it pub or export it`. Measured with
`SIMPLE_LIB=src bin/simple.exe run` probes importing the spec's exact import
list from `build/` (BEFORE: 6 `private fn` errors; the checker's per-module
error reporting is order-dependent, which is why only 6 of the 8 names were
flagged in any single run).

Fix applied (pure Simple, matches the package's own convention — the facade
`src/lib/common/json/__init__.spl` already `export use`s these names and
siblings like `json_parse`/`json_object_get`/`json_escape_string` are already
`pub`): added `pub` to the eight spec-called API fns in
`src/lib/common/json/serializer.spl` (`json_minify`, `json_beautify`),
`utilities.spl` (`json_diff`, `json_patch`, `json_unflatten_object`),
`validation.spl` (`json_deep_equals`), and `jsonl.spl` (`jsonl_is_valid`,
`jsonl_content_is_valid`). No bodies changed.

AFTER evidence: the same probe now runs to completion —
`minify={"a":1}`, `deep_equals=true`, `jsonl_is_valid=true`,
`jsonl_content_is_valid=true`, `ALL-OK`. LIMIT: the spec itself still cannot
be executed end-to-end on this host — `bin/simple.exe test` fails repo-wide
at HEAD with `unknown decorator '@representation_boundary'` (known
source/binary inconsistency at release/1.0.0 HEAD, not caused by this
change). The probe exercises exactly the imports and calls the spec was
blocked on.

## Closed 2026-09-13 — FIXED: stub modules are gone; spec's stale `lib.json.*` prefix corrected
- **measured**: all six named symbols exist as real source — `json_minify`/`json_beautify` in `src/lib/common/json/serializer.spl`, `json_diff`/`json_patch`/`json_unflatten_object` in `utilities.spl`, `json_deep_equals` in `validation.spl`; `find src/lib -name '*.smf'` returns nothing.
- **measured**: the residual failure was a stale import prefix, not a stub — `use lib.json.serializer` errors `E1034 module path segment 'json' not found` (there is no `src/lib/json/`), while the same eight imports under `std.common.json.*` all resolve and run (`all-imports-ok`, and `json_minify`/`json_deep_equals` execute).
- **FIX APPLIED**: `test/01_unit/lib/common/json_logic_spec.spl` lines 4-11 rewritten `lib.json.` -> `std.common.json.`, matching line 12 which already used that prefix.
- **inferred**: the spec was not re-run end to end; `bin/simple test` is broken on this Windows host (a trivial spec reports a false `outer-bound-timeout`).

**Date:** 2026-06-26
**Status:** CLOSED 2026-09-13; re-opened and re-fixed 2026-11-25 (see top section — seed privacy enforcement)
**Classification:** missing-source (both-fail)

## Summary

`test/01_unit/lib/common/json_logic_spec.spl` cannot load on either the seed runner or
STAGE4 because three of its imports resolve to 179-byte placeholder `.smf` stubs with no
exported symbols.

## Failing imports

| Import | Missing symbols |
|--------|----------------|
| `lib.json.serializer` | `json_minify`, `json_beautify` |
| `lib.json.utilities` | `json_diff`, `json_patch`, `json_unflatten_object` |
| `lib.json.validation` | `json_deep_equals` |

`lib.json.array_ops` (imported transitively by `path_ops`) is also a stub, but
`path_ops` does not call `json_array_get` in the tests exercised here, so it is a
latent blocker rather than an immediate one.

## Error

```
error: semantic: Cannot resolve module: lib.json.serializer
```

## What was fixed in this session

The two in-scope logic bugs that would block the spec once the stubs are
replaced were fixed:

1. **`}}` string-literal collapse** — Simple string literals treat `}}` as an
   escaped `}` (one character). The call on line 16 of the spec passed a
   truncated JSON string (`{"user":{"name":"Ada","scores":[1,2]}` with the
   outer `}` missing). Fixed by adding one extra `}` so the literal ends in
   `}}}` (produces `}}`).

2. **Missing `src/lib/common/text_advanced.spl`** — `builder.spl` imports
   `escape_json` from `common.text_advanced`, which existed only as a 179-byte
   stub. Restored `text_advanced.spl` from the agent worktree (contains only
   `escape_json`; broader helpers deferred per the TODO in that file).

Both fixes verified Passed: 5 / Failed: 0 on seed and STAGE4 via
`test/01_unit/lib/common/json_scope_check_spec.spl` (scratch spec, not landed).

## Required follow-up (out of scope)

Implement `src/lib/common/json/serializer.spl`, `utilities.spl`, and
`validation.spl` to replace the stubs. The spec can then be run in full.

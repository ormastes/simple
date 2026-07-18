# Bug: json_logic_spec blocked by stub-only json sub-modules

**Date:** 2026-06-26
**Status:** Open
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

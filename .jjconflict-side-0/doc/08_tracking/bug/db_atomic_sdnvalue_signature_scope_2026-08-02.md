# db_atomic uses function-local SdnValue imports outside their scope

**Status:** FIXED / RESOLVED 2026-08-02
**Fix owner:** `codex-genuine-imports` (RESOLVED)
**Area:** `src/lib/*/db_atomic.spl`

## Finding

Both no-GC sync and no-GC async implementations use `SdnValue` in helper
signatures while importing it only inside function bodies. A body-local import
cannot own a type name used by the surrounding declaration signature.

## Acceptance

- Import `SdnValue` at module scope in both genuine implementations.
- Keep `parse` function-local where it is consumed.
- Add exact sync and adjacent async source-level regression coverage.

## Resolution

Both implementations now import `SdnValue` at module scope. Their parsing
methods retain narrow body-local `parse` imports. The signature and match arms
therefore share one genuine type owner without broadening parser ownership.

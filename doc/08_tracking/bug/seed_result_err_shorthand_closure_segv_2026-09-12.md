# Seed segfaults on `Result` Err + shorthand-closure projection (`.map(_.field)`)

- **Filed:** 2026-09-12
- **Component:** Rust seed (`bin/simple.exe`, 2026-09-02 build), `run` path
- **Severity:** high — crashed 8 of 19 Simple MCP tools; client sees the stdio
  pipe close (`CONNECTION_CLOSED`), not an error response.
- **Status:** open. Worked around in
  `src/lib/nogc_sync_mut/storage_roots/environment_owner.spl`; the workaround
  must be reverted to the compact form once this is fixed.

## Symptom

A program that both constructs a `Result` carrying an `Err` and applies a
shorthand-closure field projection (`_.field`) via `.map` **segfaults**
(rc=139). The crash point is not stable: it has been observed at the `.map`
call, and at the plain call that merely *returns* the `Err`, in two files that
differ only in statement layout. That instability is itself part of the report.

## Minimal reproduction

```simple
struct Inner:
    value: text
struct Insp:
    roots: Inner
fn baseErr() -> Result<Insp, i64>:
    Err(42)
fn viaMap() -> Result<Inner, i64>:
    baseErr().map(_.roots)
fn main() -> i64:
    val b = baseErr()
    eprint "E1 base.is_err=" + str(b.is_err())
    val r = viaMap()
    eprint "E2 mapped.is_err=" + str(r.is_err())
    0
```

```
$ timeout 90 ./bin/simple.exe run /tmp/p16.spl >/dev/null 2>/tmp/e16.txt
Segmentation fault
rc=139
E1 base.is_err=true          <- printed
                              (E2 never printed)
```

Reproduces identically with `SIMPLE_BACKEND=interp` (rc=139), so it is not
selected by that switch.

## What is NOT the cause (each verified in isolation, all rc=0)

- `Result<Struct>.unwrap()` then nested field access — passes.
- A module-level `var _cache: Struct? = nil` cache with `Some(x)` / `x!` — passes.
- A struct with a `u32` field — passes.
- `sha256_text(...).substring(0, 24)` — passes.
- `Ok(...)` + `.map(_.field)` (the **Ok** path) — passes, value correct.
- A `text?`-returning `match` with `Some(...)` arms and `_: nil` — passes.

The fault needs an `Err` in flight *and* the shorthand closure in the same
compilation unit. The tree-walking implementation reads correctly:
`handle_result_map_operation`
(`src/compiler_rust/compiler/src/interpreter_helpers_option_result.rs:136-170`)
short-circuits on the non-matching variant and never evaluates the lambda, and
`unwrap` on `Err` raises a proper semantic error
(`interpreter_method/special/types.rs:416-439`). So the defect is most likely in
generated code rather than in those branches — the seed JITs during `run`, and
emits `compiler_cross_module_private_symbol_collision` warnings on this tree.
**Not conclusively localized.**

## Observed downstream effect

`src/lib/nogc_sync_mut/storage_roots/environment_owner.spl:61-66` used the
compact form:

```simple
pub fn resolve_ambient_storage_roots(worktree_metadata: text) -> Result<StorageRoots, StorageRootError>:
    inspect_ambient_storage_roots(...).map(_.roots)
```

On Windows `inspect_ambient_storage_roots` legitimately returns `Err`. The
`.map` then yielded a value that reported `is_err() == false`, whose `unwrap()`
returned a corrupt struct; the first field access on it segfaulted. Chain:

`tools/call` -> `handle_cli_passthrough_direct`
(`src/app/mcp/cli_passthrough.spl:43`) -> `_storage_environment_prefix`
(`:20`) -> `tooling_child_environment`
(`src/lib/nogc_sync_mut/storage_roots/tooling_paths.spl:63`) ->
`resolve_ambient_storage_roots` -> **SIGSEGV**.

Every MCP tool routed through `handle_cli_passthrough_direct` died:
`simple_build`, `simple_check`, `simple_fix`, `simple_format`, `simple_lint`,
`simple_run`, `simple_test`, `simple_tree` (8 of 19). Tools with dedicated
handlers were unaffected.

## Workaround in place

`resolve_ambient_storage_roots` is written as an explicit `is_err()` / `Ok(...)`
split instead of `.map(_.roots)`. The compact form is the one that should work;
per CLAUDE.md the workaround is recorded here rather than silently normalized.

## Related, found while investigating (separate defects, not filed here)

1. `process_run("sh", ["-c", "... exit 7"])` returns exit code **56**, not 7.
   `cli_passthrough.spl` branches on `exit_code == 124` to report TIMEOUT, so
   that branch is unreachable/unreliable.
2. `_mcp_read_message()` is declared `-> (text, bool)` at
   `src/app/mcp/main.spl:281` but every path returns `text`. The interpreter
   tolerates it; a phase-2 native compile may not.
3. Storage-root resolution still ends in `Err` on this Windows host, so the 8
   tools above now return a clean
   `centralized child storage environment is unavailable` instead of crashing.
   They return, but they are **not yet functional on Windows** — a separate,
   still-open defect.

   Not yet localized. Instrumenting `_repository_root`
   (`environment_owner.spl:15-26`) showed it returning on the **first** loop
   iteration (the `RR probe=` trace never printed), i.e. `.git` *was* found, so
   the repository root is detected and is not the cause. The `Err` therefore
   originates later, inside `inspect_storage_roots`
   (`src/lib/nogc_sync_mut/storage_roots/resolver.spl`), which has not been
   traced.

   One observation worth carrying into that investigation, stated as an
   observation and not a diagnosis: on this host `path_absolute()` returns the
   Windows extended-length form, e.g.
   `path_absolute("C:\Users\ormas\dev\simple")` ->
   `\\?\C:\Users\ormas\dev\simple`. Downstream code that appends `"/..."` to
   such a path is mixing a `\\?\` prefix with forward slashes, and `\\?\` paths
   are passed to the OS without normalization. Whether any `inspect_storage_roots`
   path depends on that has not been checked.

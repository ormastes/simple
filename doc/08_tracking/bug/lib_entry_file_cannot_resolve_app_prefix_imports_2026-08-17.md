# `use app.*` is unresolvable when a `src/lib/**` file is the entry file (E1034)

- **Filed:** 2026-08-17 (lane IMPORTFIX)
- **Status:** OPEN — filed, not fixed. The import path is CORRECT; the defect is in module-root selection.
- **Severity:** P2 — no production lane is currently broken by it, but it makes every
  `src/lib/**` file that imports `app.*` unusable as a run/probe target, and it silently
  hides real import breakage behind stale `.smf` artifacts.

## Verbatim error

```
$ bin/simple run src/lib/nogc_sync_mut/test_runner/main.spl
error: SIMPLE_JIT_STRICT: HIR lowering error: cannot resolve import `app.test_daemon.session_types`:
Module resolution error: SemanticWithContext(ContextualError {
  message: "cannot resolve import: module path segment `app` not found",
  context: ErrorContext { span: None, secondary_spans: [], file: None, source: None,
    code: Some("E1034"),
    notes: ["ensure the module file or __init__.spl exists"],
    help: ["check that the module exists at \"src/lib/nogc_sync_mut/test_runner/app\""] } })
[in src/lib/nogc_sync_mut/test_runner/main.spl]: unresolved import; refusing to fall back to the interpreter
```

rc=1 (captured on the line after the command, not through a pipe).

## The import target is NOT missing

`src/app/test_daemon/session_types.spl` exists (11550 bytes) alongside
`src/app/test_daemon/__init__.spl`. Both run clean as entry files themselves
(`bin/simple run` on each: rc=0, zero `cannot resolve import`). Nothing was moved,
renamed, or deleted. Do not "fix" this by rewriting the import path.

## Root cause: the module root is the ENTRY FILE'S DIRECTORY

The `help` line gives it away — the resolver looked for the `app` root at
`src/lib/nogc_sync_mut/test_runner/app`, i.e. relative to the entry file, not at the
repo `src/`. When the same lib module is loaded as a *library* from an app entry under
`src/app/**`, the root is `src/` and `app.test_daemon.session_types` resolves fine. That
is why this has sat unnoticed: the import only breaks on the run-as-entry path.

## Why it looks intermittent — stale `.smf` masks it

`use app.*` from a `src/lib/**` entry succeeds **iff** a prebuilt `.smf` exists for the
target package. Perfect correlation across three probes:

| entry file (all under `src/lib/nogc_sync_mut/`) | import | `src/app/<pkg>/__init__.smf` | rc |
|---|---|---|---|
| `lsp/main.spl` | `app.lsp.lsp_json` | present | 0 |
| `lsp/transport.spl` | `app.protocol.transport.{...}` | absent | 1 (E1034) |
| `test_runner/main.spl` | `app.test_daemon.session_types.*` | absent | 1 (E1034) |
| `test_runner/test_classification.spl` | `app.test_daemon.session_types.{...}` | absent | 1 (E1034) |

`src/app/protocol/` and `src/app/test_daemon/` both exist as source. Only the compiled
artifact differs. So the "working" case is not source resolution working — it is a stale
build product papering over the same defect.

Import *form* is not a factor: temporarily rewriting line 62 of `main.spl` to the plain
`use app.test_daemon.session_types` (no `.*`) still failed, one segment shallower
(``cannot resolve import `app.test_daemon` ``). The file was restored byte-for-byte
(`git diff` empty) after the experiment.

## Is `main.spl` live or dead? — DEAD

`src/lib/nogc_sync_mut/test_runner/main.spl` has no real consumer.

- The live runner is `src/app/test_runner_new/test_runner_main.spl`. It imports ~12
  `std.test_runner.*` modules by explicit brace list and **never** imports
  `std.test_runner.main`.
- Every importer of `test_runner.main` in the tree is a self-referential compatibility
  facade that only re-exports it onward and is itself imported by nobody:
  - `src/lib/nogc_async_mut/test_runner/main.spl:1` → `export use std.nogc_sync_mut.test_runner.main.*`
  - `src/lib/gc_async_mut/test_runner/main.spl:1` → `export use std.nogc_async_mut.test_runner.main.*`
  - `src/lib/gc_sync_mut/test_runner/main.spl:3` → `export use std.gc_async_mut.test_runner.main.*`
- `src/lib/nogc_sync_mut/test_runner/__init__.spl:89` has `export main`, so a barrel
  wildcard would pull it — but no consumer uses a wildcard barrel import; all observed
  call sites are explicit `.{...}` lists.

So `bin/simple test` does not reach it. Deleting it (per the implement-or-delete rule)
would require also removing the three facade files above, which are outside this lane's
ownership — hence filed rather than deleted.

## Fix directions (not attempted here)

1. **Real fix:** make the module root for a `src/lib/**` entry file be the workspace
   `src/` (walk up to the source root / `simple.sdn`) rather than the entry's own
   directory, so `app.` and `std.` resolve identically whether a lib module is the entry
   or an import.
2. **Separately:** decide the fate of `main.spl` + its three facades — they are dead
   weight and one of them is unrunnable.

## Reproduce

```bash
bin/simple run src/lib/nogc_sync_mut/test_runner/main.spl   # rc=1, E1034
bin/simple run src/app/test_daemon/session_types.spl        # rc=0 — target is fine
bin/simple run src/lib/nogc_sync_mut/lsp/transport.spl      # rc=1, same shape, different pkg
bin/simple run src/app/test_runner_new/test_runner_main.spl # rc=0, 0 unresolved — CONTROL
```

The last line is the control that pins the root cause: the live runner under `src/app/**`
pulls in the same `std.test_runner.*` modules and resolves everything (rc=0, zero
`cannot resolve import`). Only the entry file's location differs.

Do not use `bin/simple check` (>600s). Do not bisect with `head -N` — cutting mid-block
manufactures its own error so every prefix appears broken.

# native-build --backend llvm: "llc not found" x1427 although llc.exe is on PATH

Registered 2026-11-16. Status: open. Severity P2.

## Symptom

In a 1,542-module `native-build --backend llvm` run by the frozen Phase 2
compiler (pin `18a1f28937c2`), codegen reported 1,427 x `llc not found` while
`llc.exe` exists on PATH (msys2 clang64; llvm-mingw ships no llc). Free memory
was about 3 GB at the time.

## What the code does (read at origin/release/1.0.0 115bd321a44)

- `src/compiler/70.backend/backend/llvm_backend_tools.spl:466-470`: per AOT unit,
  `val llc = find_llc()`; `val clang = if llc == "": find_clang() else: ""`;
  `if llc == "" and clang == "": return llvm_object_stage_fail(..., "llc not
  found", 1)`. So the message is emitted when BOTH llc and clang resolve to the
  empty string. The text does not say whether a probe failed or the tool is
  absent.
- `src/compiler/95.interp/interpreter/llvm/tools.spl`: `find_llc()` (line 192)
  calls `_find_tool([...])` (line 98). `_find_tool` HAS a per-process cache
  (lines 87-96, 120-137, commit 73a12be2d25, 2026-10-25, an ancestor of the
  pin): a hit is cached for the process lifetime, but a miss is cached only as a
  counter and retried until `_FIND_TOOL_MAX_MISSES = 3`, after which `""` is
  cached permanently. This contradicts "re-probes per unit"; the probe is not
  per unit once cached.
- `_find_tool_discover` (line 139) order: env dirs (`SIMPLE_LLVM_BIN`,
  `LLVM_SYS_231_PREFIX`, `SIMPLE_LLVM_WIN_ROOT_23`, `LLVM_SYS_180_PREFIX`) with
  `file_exists` + `_tool_runs` (spawn `--version`, exit 0 required); then per
  candidate: in-process PATH scan (`backend_tool_on_path`) + `_tool_runs`; then
  `where <candidate>` via a shell subprocess, each hit run with `--version`.
  Any failed spawn (`process_run` nonzero/-1) is indistinguishable from "tool
  absent" and yields `""`.

## Hypothesis (not confirmed)

Under memory pressure the `--version` / `where` subprocess spawn fails
transiently. The first 3 calls that fail (possibly concurrent units across
workers, or any three early failures) exhaust the bounded retry, and `""` is
then cached for the rest of the process, producing the long run of
`llc not found`. That would explain why a count in the thousands appears even
though the cache exists: a few transient failures become permanent. If the
build runs codegen in several worker processes, each has its own cache.

## Workaround

Pin `SIMPLE_LLVM_BIN=<dir containing llc.exe>`. With it set, a rerun showed 0
occurrences through HIR+MIR; codegen confirmation is pending.

## Proposed fix (proposal only)

1. Resolve each tool once per process at startup (before heavy allocation) and
   cache the success; never cache a transient failure as a permanent `""`.
2. Distinguish "probe failed" (spawn error / nonzero `--version`) from "not
   found" (no candidate file exists) and report it in the message, including
   the candidate path tried and exit code.
3. Prefer a cheap non-spawn existence check, and retry a failed probe with
   backoff before giving up.

## Status

Open. Compiler code not changed by this registration.

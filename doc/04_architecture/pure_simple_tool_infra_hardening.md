<!-- codex-design -->
# Pure-Simple tool and infrastructure hardening architecture

## Decision

Harden existing owners instead of adding a parallel framework. The production
boundary is a chain of small fail-closed contracts:

1. candidate admission proves runtime provenance;
2. launchers select only admitted cached artifacts;
3. tools preserve process and semantic failure information;
4. qualification runs the same production routes users invoke.

No MDSOC transform is needed. These are existing infrastructure capsules with
explicit boundaries, not cross-cutting business behavior.

## Owners

| Concern | Canonical owner | Consumers |
|---|---|---|
| Candidate provenance/admission | existing redeploy-gate helper | bootstrap, setup, Unix/Windows launchers |
| CLI command inventory | `app.cli.dispatch.table` | dispatch statistics/help/qualification |
| Test file outcome | test-runner result/parser modules | single runner, main runner, daemon |
| Nested-test routing | test daemon/client | runner-launched child processes |
| File discovery/read | stdlib IO facades | duplicate checker |
| Lint attributes/results | compiler lint configuration and `Linter` | CLI lint wrapper |
| Format/fix behavior | one `app.io` CLI handler | thin command entrypoint |
| MCP/LSP artifact selection | generated launcher templates | checked-in launchers/installers |
| Qualification | production-path SPipe spec | verify/release gates |

## Invariants

- A production path never accepts a binary whose runtime identity says seed or
  debug, regardless of its filename or directory.
- Parsed child output may add detail but never erase nonzero process failure.
- A partial test execution is failure, including sibling groups silently not
  executed.
- Daemon-owned children never enqueue work back to the same serial daemon.
- CLI-controlled paths remain data passed to Simple IO APIs, never shell text.
- Wrappers contain selection/adaptation only; behavior stays in one owner.
- Cache hits are observationally equivalent to misses and invalidation follows
  every relevant input/config/tool-version change.

## Test outcome contract

Expose these stable CLI outcome classes at the single top-level boundary:

| Class | Exit code | Meaning |
|---|---:|---|
| `pass` | 0 | all selected examples executed and passed |
| `assertion_failure` | 1 | one or more examples failed |
| `usage_error` | 2 | invalid arguments/configuration |
| `internal_error` | 3 | child/runner infrastructure failure |
| `empty_discovery` | 4 | no runnable examples without an explicit filter allowance |
| `timeout_resource` | 124 | timeout or enforced resource termination |

Existing `TestFileResult` remains the internal carrier. Add the smallest pure
classifier at the CLI boundary; do not introduce a second result hierarchy.

## Runner execution

The child process exit is authoritative. If it is nonzero, the result is never
OK even when stdout contains a green-looking summary. The runner compares
authored runnable examples with executed examples for interpreter SSpec files;
count mismatch is `internal_error`. A daemon child receives an explicit marker;
the client detects the marker and directly invokes the no-daemon runner.

Parent memory is bounded by fixed-size batch re-exec using the same command and
serialized options. This is deliberately simpler than adding a new allocator or
long-lived worker pool.

## Duplicate and lint paths

Duplicate-check uses `dir_walk_native` plus existing exclusion/wildcard logic
and `file_read`. Semantic extraction loops over those files through the existing
Simple parser. Shell batch acceleration is removed because it is both unsafe and
a second implementation.

CLI lint calls `Linter.lint_source`, which already applies canonical file
attributes and levels. Lint/fmt/fix have one handler; the command entrypoint
calls it directly or invokes a validated cached worker only when isolation is
required.

## MCP/LSP startup, caches, and invalidation

Startup order is cached native candidate, correlated protocol probe, then
fail-closed diagnostic. Raw source and Rust seed/debug are not production
fallbacks. Generated and checked-in launcher defaults are identical.

The hot request path stays inside the already-started server; no per-request
binary probing or full-tree scan is added. Native artifacts invalidate on entry
source closure, compiler/runtime version, target, build flags, or manifest
change. Index caches additionally invalidate on create/edit/move/delete/rename,
template application, and bulk replace through their existing owners.

## Observability

Qualification records runtime path/hash/identity, selected artifact class,
outcome class, elapsed time, max RSS, cache hit/miss state, and correlated MCP or
LSP request ID. Human output may summarize these fields; retained evidence uses
stable key/value or JSON data.

## Failure and rollback

Deployment validates before swap, preserves only an already-admitted old target, probes the new
target, and restores the old target on any failure. A missing native MCP/LSP
artifact or failed protocol probe is a production error, not permission to run
raw source.

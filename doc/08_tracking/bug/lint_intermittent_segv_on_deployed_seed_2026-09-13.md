# `simple lint <file>` intermittently SEGVs (rc 139) on the deployed seed
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (2026-09-13)
- Binary: deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 `3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`
- Host: aarch64, 20 cores, shared box at load ~40
- Found by: lane PERF-4 while baselining
  `subcommand_help_loads_implementation_closure_2026-09-12.md`. Out of that
  lane's scope, filed rather than fixed.

## Symptom

`simple lint <path>` exits **139** (SIGSEGV) with empty stdout instead of
printing its verdict. It is intermittent, and markedly more likely under
`strace -f`:

| invocation | runs | rc 139 |
|---|---:|---:|
| `lint <2-line file>` under `strace -f -e trace=openat` | **6** | **6** |
| `lint --help` under the same strace | 1 | **1** |
| `lint <2-line file> --help` under the same strace | 1 | **1** |
| `lint <2-line file>`, no strace | 3 | **1** |
| `lint --help`, no strace | 3 | 0 |

The crashing runs reach 533-536 `.spl` opens — i.e. the whole lint closure has
already been loaded — so this is not an early-startup failure.

A successful run of the same command prints `Lint passed: all files clean`
(rc 0), so the crash is not input-dependent for this file.

## Why it matters

`lint` is a gate surface: `scripts/check/lint-cached.shs` caches CLEAN verdicts,
and a run that dies with rc 139 and no verdict line is indistinguishable at a
glance from a tooling error. It also makes any lint-based measurement flaky, and
it silently reduces the evidence value of "lint passed" in a receipt.

## Repro

```sh
b=bin/release/aarch64-unknown-linux-gnu/simple
printf 'fn main() -> i64:\n    0\n' > /tmp/probe.spl
for i in 1 2 3 4; do
  strace -f -e trace=openat -o /tmp/tr $b lint /tmp/probe.spl >/dev/null 2>&1
  echo "rc=$?"
done
```

## Not reproduced on the lane's rebuilt seed — and that is a real signal

A seed built from `f26970e9d93` plus PERF-4's help-routing commit
(sha256 `391885bad8d0e2db...`) ran the SAME loop with **rc 0, 4/4** (514 `.spl` opens each). The
deployed seed crashed 6/6 in that configuration, so this is not luck, and it is
not explained by PERF-4's change either: that change is confined to
`driver/src/main.rs` dispatch routing and does not run on `lint <file>` at all.
The most likely reading is that the deployed binary predates some already-landed
fix, i.e. the defect may be gone at `origin/main` and alive only in the artifact
everyone is actually running. Whoever picks this up should start by diffing the
deployed seed's provenance against `f26970e9d93` rather than by hunting the
crash.


## CLOSED 2026-11-09 — stale (not reproducible on the current seed)

Re-checked on the current deployed seed (Windows x86_64, `bin/simple.exe`,
sha256 prefix `8c7341592f4d47de`, release/1.0.0 at `f7e0be6779b`), host idle:

| invocation | runs | rc >= 128 (crash) | observed rc |
|---|---:|---:|---|
| `lint probe.spl` (`fn main() -> i64:` / `0`, the record's probe) | 20 | 0 | 1 x20 (deterministic `STUB002` finding, verdict printed every run) |
| `lint probe2.spl` (`fn main():` / `print("hi")`) | 30 | 0 | 0 x30, `Lint passed: all files clean` |
| `lint src/lib/common/base_encoding.spl` | 10 | 0 | 0 x10, `Lint passed: all files clean` |

Every run printed its verdict line; no empty-stdout exit and no signal exit in
60 invocations. This matches the record's own finding that a seed rebuilt from
`f26970e9d93` already ran 4/4 clean — the crash lived only in a stale deployed
aarch64 artifact (`3d120a6f...`) that no longer exists as a tooling surface.
The strace-amplified lane cannot be replayed on Windows, but the no-strace
intermittent case (1/3 in the record) did not reproduce in 60 runs.

Closed as stale; reopen with a fresh crash transcript against a named current
binary if it recurs.

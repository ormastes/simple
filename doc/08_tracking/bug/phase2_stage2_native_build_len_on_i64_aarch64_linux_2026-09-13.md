# Phase 2 (Stage 2) native-build cannot complete on aarch64 Linux: `method \`len\` not found on type \`i64\`` with no location
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-09-13, FULLTEST lane (`work/fulltest-phase2-2026-09-13`).
**Status:** OPEN — this is the SAME class as
`full_cli_selfhosted_native_build_blockers_2026-08-27.md` Blocker A and
`mcp_stdio_smoke_seed_flat_registry_len_i64_2026-07-17.md`, re-confirmed here
on a different arch/OS (aarch64 Linux vs. that record's x86_64) and at a
smaller scale (Stage 2 itself, not the ~1872-module full-CLI closure).

## What was tried

Goal: build "phase 2" (the pure-Simple compiler compiled by the Rust seed —
Stage 2 per `doc/07_guide/compiler/build.md`) to run the test suite under it.

1. The deployed seed (`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
   2026-09-06) fails `native-build` immediately on even a 2-line hello world
   with `error: semantic: unknown extern function: rt_env_vars`. Root-caused
   to a stale binary: `rt_env_vars` was registered in the interpreter's
   extern dispatch table by commit `e74e4f6a274c` (2026-09-09), 3 days after
   this binary was built. Fixed by building a private seed from current
   source (`CARGO_TARGET_DIR=/home/yoon/dev/cargo-fulltest cargo build
   --release -p simple-driver`, hardlink-cloned target dir, ~1m21s build) —
   `bin/simple` itself was never touched, per policy.
2. With the fresh seed, the SAME hello-world `native-build` advances past
   `rt_env_vars` and fails differently:
   ```
   SCV-E-SNAPSHOT: snapshot-inventory-unavailable
   error: semantic: method `len` not found on type `i64` (receiver value: 0)
   native-build worker exited with code 1. interpreter: <fresh-seed>
   ```
   No file:line. Deterministic (identical with `--threads 1`, `--low-memory`,
   `SIMPLE_STRICT_EXTERN=1` — the last of which also proves it is NOT an
   unbacked-extern-returns-nil case; STRICT_EXTERN never names an extern).

## One real, distinct, FIXED bug found and landed along the way

The `SCV-E-SNAPSHOT: snapshot-inventory-unavailable` line is not cosmetic: it
was `_nb_scv_freeze_v1` (`src/app/io/_CliCompile/native_build_closure.spl`)
failing because NO worktree on this host has an admitted SCV source
inventory (`build/scv/CURRENT` / `.simple/scv/CURRENT` — confirmed absent
everywhere by a repo-wide `find`; the inventory is maintained purely by an
external event-submitting adapter that nothing here runs), and its caller,
`_native_build_entry_closure`, returned `[]` outright on that failure instead
of falling back to reading the working tree directly. That collapsed every
`--entry-closure` computation to an empty file list. Fixed to fall back to
the unfrozen `entry`/`source_dirs` (i.e. behave as if SCV were never
consulted) instead of aborting. TDD: RED spec first
(`test/01_unit/app/io/_CliCompile/native_build_entry_closure_scv_fallback_spec.spl`,
using the pre-existing but previously-unreferenced fixture
`test/fixtures/native_build_closure/`), GREEN after the fix, verified under
phase 1 (the deployed seed). Commit: see this branch's history for
`fix(native-build): fall back to a direct scan when SCV freeze has no admitted inventory`.

**This fix does NOT unblock hello-world native-build.** Isolated
function-level testing (calling `_native_build_entry_closure` directly on the
8-file test fixture) proves the fallback works and returns the full closure.
But the real `native-build` CLI path still fails identically on hello world
after this fix, because native-build must first load/interpret the compiler's
OWN ~1800+-module source graph to become capable of compiling anything — the
entry-closure code for the TARGET program is reached, if at all, well after
that point. The `len`-on-`i64` crash therefore has nothing to do with the
target program's size; it reproduces for a 2-line hello world exactly as it
would for a large one, because the "large closure" that matters is the
compiler's own.

## Why this matches Blocker A / the 07-17 registry-corruption class

`full_cli_selfhosted_native_build_blockers_2026-08-27.md` describes, building
the FULL CLI (`src/app/cli/main.spl`, ~1872 modules) with the SEED:
`error: semantic: method \`len\` not found on type \`i64\` (receiver value: 265)`,
"No file:line; single-threaded rerun does not localize it... an unrelated
call corrupts to i64 when a large import closure is present." That record
also states the seed DID successfully build Stage 2 previously (stage2 hash
== stage3 hash `ce895e970d70`). Here, the SAME error class blocks Stage 2
itself (a smaller closure than the full CLI), with a different receiver
value (0 vs 265) — consistent with "an unrelated call corrupts to i64",
where WHICH call gets corrupted, and what garbage value results, depends on
closure contents/size at the time. Plausible explanation for the regression
between "Stage 2 built fine" (as of 08-27) and "Stage 2 fails identically to
the full-CLI case" (now, 09-13): the codebase has grown in the intervening
~2.5 weeks, and Stage 2's closure has crossed whatever threshold triggers the
corruption.

## Why this is not fixed here

This is a deep, previously-triaged, OPEN interpreter defect (whole-program
registry corruption under a large import closure) with no location
information and no known root cause after prior investigation ("single-
threaded rerun does not localize it"). It is not a small self-contained
`src/compiler/**` lowering bug and not a `≤20`-line `src/compiler_rust` fix
covered by a spec, so per this lane's rules it is filed, not fixed.

## Consequence for this FULLTEST lane

Phase 2 (Stage 2) cannot currently be built via `native-build` on this host
with either the deployed or a freshly-rebuilt seed. Running the test suite
"under phase 2" is therefore blocked at the very first step — before any
compiler-lowering bug (loop-carried accumulator, `str()` return value, etc.
per the sibling `phase2_*_2026-09-13.md` records, all measured on Windows)
can even be reached on this host/arch. See the lane's receipt,
`RECEIPT_FULLTEST.md`, for the full write-up.

## Suggested next step for whoever picks this up

Bisecting `.spl` source alone with a SEED FIXED at current HEAD does **not**
work: tried checking out `0fce018eda3` (PR #91, "bootstrap-fixpoint" — the
commit the 08-27 record cites as its last known-good Stage 2) in an isolated
`git worktree` and running the current fresh seed against it. It fails too,
but with yet another error shape — `method \`len\` not found on type \`nil\`
(receiver value: nil)` instead of `i64` — which is consistent with an old
`.spl` tree being genuinely incompatible with a 2.5-weeks-newer interpreter
(stdlib/interface drift), not a clean re-observation of the same bug. A
seed built from 2026-09-13 source cannot safely interpret 2026-08-27 source;
the two must be bisected TOGETHER. A real bisection needs, at each candidate
commit: `cargo build --release -p simple-driver` from THAT commit's own
`src/compiler_rust` (paired with its own `.spl` tree) via a private
`CARGO_TARGET_DIR`, then the hello-world `native-build` probe against that
matched pair. Each step is then a cargo build (incremental, warm cache,
~1-3 min observed) plus a ~1 min run — expensive enough that only a bounded
number of probes was affordable in this session; not completed here.
`git bisect` over `src/compiler`, `src/lib`, `src/app` between `0fce018eda3`
and `origin/main` (990 commits touching those paths) with the above
matched-pair probe as the bisect script is the mechanical next step.


## No longer reproducible at current source — 2026-11-05

Two independent verifications at current release/1.0.0:

1. The trust-root bootstrap built Stage 2 itself on this host (aarch64
   Linux): 1567 modules compiled and linked by the seed, sanity gate PASS.
   This is the exact operation this doc records as impossible (the blocking
   closure was the compiler's own graph, which the bootstrap compiles
   end-to-end).
2. The doc's precise recipe — deployed seed running native-build of a
   2-line hello world, forcing the seed to load/interpret its own
   ~1800-module source graph — ran for 900s (hit the probe timeout, still
   compiling) with ZERO occurrences of `method 'len' not found on type
   'i64'`; bootstrap error counts at every recorded point were 0. On
   2026-09-13 this failure was immediate and deterministic.

The registry-corruption defect does not reproduce at current source. Not
claimed: the probe build did not complete within the window (it is slow, not
failed); the stage2 compiler-test matrix end-to-end result remains the
final acceptance for running the suite under stage 2.

## 2026-11-09 — location diagnostic landed (fix-implemented-verification-pending)

`bail_unknown_method!` (`src/compiler_rust/compiler/src/interpreter/error_macros.rs`)
now attaches `while evaluating module: <file>` (and sets the error's file) on
every unknown-method error, and with `SIMPLE_BOOTSTRAP_DIAG=1` adds the 12
innermost interpreted functions as a note plus an `[unknown-method]` stderr
line. Next aarch64 Linux run: rerun the failing `native-build` with
`SIMPLE_BOOTSTRAP_DIAG=1` and record the module + call stack here. cargo not
run on Windows (disk < 30 GB); needs a seed rebuild to take effect.

---

## Addendum 2026-11-11 (lane boot7) — SUPERSEDED-by-prior-lane; spot-check found the 2026-11-09 diagnostic incomplete for this row's exact error shape

This doc already carries verified addenda from earlier lanes: 2026-11-05 (defect
no longer reproducible at current source — trust-root bootstrap built Stage 2 on
aarch64 Linux, 1567 modules, sanity gate PASS; 900 s hello-world probe with zero
`len`-on-`i64` occurrences) and 2026-11-09 (location diagnostic landed,
fix-implemented-verification-pending). Spot-checks at tip b364745fdbf8:

1. **Headline defect** (native-build blocked by `method 'len' not found on type
   'i64'` under the compiler's own closure): accepted as SUPERSEDED per the
   2026-11-05 verified addendum. Not re-run here: the repro needs the aarch64
   Linux bootstrap (Windows host, and native/entry-closure builds are forbidden
   in this lane).

2. **2026-11-09 location diagnostic — spot-check: INCOMPLETE for this row's
   error shape.** The landed fix (cf52b105306b, "diag(seed): unknown-method
   errors carry module file + interpreted call stack", an ancestor of the
   2026-11-11 seed build 0791c2b7f4a7) attaches `while evaluating module:
   <file>` only inside the `bail_unknown_method!` macro
   (src/compiler_rust/compiler/src/interpreter/error_macros.rs:89-91). This
   row's exact error text — `method 'len' not found on type 'i64' (receiver
   value: N)` — is raised from a DIFFERENT site, the primitive dispatch tail at
   src/compiler_rust/compiler/src/interpreter_method/mod.rs:2050-2075, which
   builds its `ErrorContext` manually and does NOT carry the module note.
   Seed-smoke (2026-11-11, refreshed seed 0791c2b7f4a7): `val x: i64 = 5;
   print(x.len())` under SIMPLE_EXECUTION_MODE=interpret, with and without
   SIMPLE_BOOTSTRAP_DIAG=1, prints the bare
   `error: semantic: method 'len' not found on type 'i64' (receiver value: 5)`
   with NO module file, NO note, NO call stack. This is exactly the gap the
   pinning test 51954450aa61 documents ("the primitive dispatch tail builds its
   ErrorContext manually and does NOT yet carry the module note (follow-up on
   the tracking bug)").

Residual follow-up (recorded, not fixable in-lane): extend the module-note
attachment to the manual-ctx dispatch tail in interpreter_method/mod.rs so this
row's error shape is locatable too. Fix is seed-side Rust and only takes effect
after a seed rebuild (cargo not runnable on this Windows host per the 2026-11-09
note: disk < 30 GB), so no in-lane fix attempted.

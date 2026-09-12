# Stage 2 sanity fails `native-capsule-receipt-invalid` with IDENTICAL byte counts (macOS, 2026-09-12)

Status: **OPEN. Receipt sites worked around in PR #677. The "root cause"
below named the right SYMPTOM but the wrong TRIGGER: a compiler-fix lane
reproduced none of it at T1 from four probes, up to and including the verbatim
pre-#677 receipt code using the real `FileFingerprint` — see the 2026-09-12
follow-up section before acting on the section immediately below.**
**Supersedes the Stage-2 `serialize_mir_function` SEGV as lane 1's Stage-2
blocker** — see "The SEGV did not reproduce" below before scheduling any work
against that older item.

## Root cause: an `i64` struct field read through an optional binding returns a BOX

This record asked for the first differing offset and the two bytes there. That
was added (PR #670) and it answered the question on the first rerun:

```
receipt-content-mismatch:expected-bytes=1648:actual-bytes=1648
  :first-diff-line=4:expected=53657758209:actual=53657761281
```

Line 4 is the object SIZE. Both values are tagged heap pointers --
`0xc7e406a01` and `0xc7e407601` -- for a **632-byte** object file, and they are
**3072 bytes apart in the SAME process**. Reading the `i64` field `.size` off
an optional-bound `FileFingerprint` --

```
val object_fp = FileFingerprint.from_file(object_path)
if val fp = object_fp:
    ... "{fp.size}" ...
```

-- yields a fresh BOX per read under Stage-2 native codegen. The receipt is
WRITTEN from one such read and VERIFIED by recomputing it, so the two could
never agree, while being the same LENGTH. That is the whole of the reported
symptom.

`.content_hash` through the identical binding looked correct, and that is why
this survived two rounds of investigation: a `text` field IS a pointer, so a
boxed read of it is indistinguishable from a correct one. Only the `i64` field
exposed the defect. This is the same family as the
`case Ok(source): source.content` misread recorded in
`stage2_capsule_source_mutated_and_unreportable_reason_2026-09-07.md`.

**Two earlier hypotheses, both disproved -- do not re-litigate them:**
- *Nondeterministic across worktrees/hosts (timestamp, absolute path, host
  triple spelling).* No. Line 4 is the only differing line, and the two values
  differ within one process.
- *A dual `rt_file_size` extern declaration (`-> usize?` in
  `src/lib/nogc_sync_mut/fs.spl` vs `-> i64` in six other modules) whose boxed
  spelling won.* Fixed in PR #670 -- correctly, since one extern symbol must not
  carry two incompatible signatures -- and the mismatch REPRODUCED unchanged
  afterwards. It was not this defect.

## What landed, and what did not

PR #677 removes every path from a struct field to the receipt: the writer and
the verifier call `rt_file_size(object_path)` directly through a file-local
`-> i64` extern, and the phase-3 materialise site reads its two values from
locals instead of building a `FileFingerprint` and reading it back. Both
runtime call sites fail closed on the -1 stat sentinel, which
`FileFingerprint.from_file` passes through unchecked.

**That is a workaround at three call sites, not a fix.** The codegen defect is
untouched and will misread any other scalar field read the same way. Whoever
takes it: the reproducer is a one-field probe -- build a struct with an `i64`
field, wrap it in an Optional, bind it with `if val`, and print the field under
Stage-2 native codegen; a pointer-shaped value means the defect is live.

## 2026-09-12 follow-up: the one-field reproducer does NOT reproduce at T1

A compiler-fix lane took the "one-field probe" instruction above literally and
could not make it fail. Four probes, each compiled by a **live Stage 1**
(the pure-Simple compiler built from `src/compiler` by the Rust seed in this
same run) and then executed, all printed the correct `632`:

| probe | shape | result |
|---|---|---|
| `disc.spl` | local `struct` + `-> S?` free fn + `if val` + `match`, fields `i64`/`i32`/`bool`/`f64`/`text`, field read twice | all correct |
| `disc2.spl` | the same across a **second module**, built by a `static fn from_file(path) -> Self?` whose `size` comes from a file-local `extern fn rt_file_size` | all correct |
| `disc3.spl` | the **real** `compiler.driver.driver_build.incremental.FileFingerprint`, `from_file` on a 632-byte file, `.size` read twice plus a second independent `from_file` | all correct |
| `disc4.spl` | the **verbatim pre-#677 receipt shape**: `val object_fp = FileFingerprint.from_file(p)` / `if not object_fp.?: return ...` / `if val fp = object_fp:` / `"...\n{fp.size}\n{fp.content_hash}\n"`, called twice | byte-identical receipts, `632` both times |

`disc4` is the load-bearing one: it is the failing code, with the real struct,
the real `.?` guard (see
`dotq_presence_operator_is_bare_unwrap_outside_argument_position_2026-09-12.md`,
which was a live suspect and is hereby ruled out for this defect), the real
five-line interpolation — and it is correct.

**So the trigger is not the source shape.** It is something about the build in
which the failing code runs: Stage 2 is the whole compiler compiled
`--entry-closure` in `dynload` mode as 834 units, and the probes are one-unit
programs that merely import the same module. Any further work should start from
that difference (unit splitting / lazy imports / dynload symbol transport), not
from the `if val` binding.

### Hypothesis examined and disproved

A read of the MIR lowering suggested this chain: `if val` promotes a binding
only for a **Float** payload
(`src/compiler/50.mir/mir_lowering_stmts.spl:2804-2814`), otherwise
`bind_local(if_val_symbol_id, if_val_raw_local)` (`:2840-2842`) leaves the name
bound to the raw Option local, which was marked `option_value_locals` +
`mark_runtime_value_local` at
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1708-1710`;
`expr_type_symbol` (`src/compiler/50.mir/_MirLowering/function_lowering.spl:1725`)
matches only `case Named(symbol, _)` so an `Optional(Named(Struct))` base loses
its owner struct; and the Field arm
(`expr_dispatch.spl:3460-3522`) emits `emit_get_field` with no
`decode_runtime_value` (`:1073`) — that unbox guard exists only on the
`??`/`!`/unwrap arms (`:4088`, `:4228`, `:4349`).

That chain is real code, but it is **not** this defect: every probe above
exercises exactly it and reads the scalar correctly. Do not edit those lines on
the strength of this record.

### Verification tier and exact commands

T0 is unavailable on this host and that is itself worth recording:

- `bin/release/aarch64-apple-darwin-macho/simple` (Sep-7) SEGVs (rc=139) on a
  three-line hello world with
  `[simple-runtime][error] rejected invalid array handle before dereference;
  probable compiler/FFI ABI mismatch`.
- `bootstrap/stage{1,2,3}/simple` are the bootstrap wrapper and answer
  `error: bootstrap_main cannot emit a seed-wrapper fallback for a.out`.
- Running the pure-Simple compiler under the seed interpreter
  (`seed run src/app/cli/bootstrap_main.spl native-build ...`) fails twice:
  without the composition it prints
  `PLUG-E-K1-POLICY: bootstrap backend composition admission failed`
  (the `--source src/compositions/kernel_llvm_cranelift` overlay the bootstrap
  passes is not a seed `run` flag), and with the composition overlaid it dies
  on `error: semantic: unknown extern function: rt_env_vars`.
- `.simple/storage/build/bootstrap/lane-stage2-rerun2.log` does not exist in a
  fresh checkout; the F44 Stage 1 referenced elsewhere is not on this host.

T1 was therefore produced by a live bootstrap, and the Stage 1 it preserves is
directly usable:

```sh
# ~3 min Rust seed (after `cp -Rc` of another checkout's src/compiler_rust/target
# -- APFS clone, per the seed-reuse note below), then Stage 1.
PATH="/usr/bin:$PATH" BOOTSTRAP_STAGE3_COMPARE_TOOL=/usr/bin/cmp \
SIMPLE_CACHE_SCOPE=codegen-optbind \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 \
     --full-bootstrap --mode=dynload --jobs=half
# Stage 1 lands at build/phase_snapshots/phase1_<epoch>/simple

# Build any single .spl through it (the env block is the script's own
# Stage1->Stage2 block, lines 2783-2818; without it the binary re-spawns
# itself as a worker and dies with "method `len` not found on type `i64`"):
env SIMPLE_BOOTSTRAP=1 SIMPLE_ABI_POLICY=simple-v1 \
    SIMPLE_PLUGIN_MANIFEST_POLICY=simple-sdn \
    SIMPLE_KERNEL_K1_POLICY=llvm-cranelift \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_NATIVE_BUILD_RUST=1 \
    SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_FRONTEND_CACHE=1 \
    SIMPLE_FRONTEND_CACHE_DIR="$CACHE/frontend" \
    SIMPLE_BINARY="$STAGE1" SIMPLE_LIB="$PWD/src" \
  "$STAGE1" native-build --target aarch64-apple-darwin --backend llvm \
    --runtime-bundle core-c-bootstrap \
    --source src/compositions/kernel_llvm_cranelift \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure --threads 4 --cache-dir "$CACHE" \
    --mode dynload --entry <file>.spl -o <out>
```

Calibrated on `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`
(prints `hello`) before any probe was trusted. Module imports resolve relative
to the **cwd**, so a probe that does `use compiler....` must be built from the
repo root.

**`SIMPLE_NATIVE_INCREMENTAL=1` now breaks the lane.** The reproduction recipe
at the top of this file sets it; at `origin/main@cf5d186754a` that aborts Stage
2 before any build with

```
error: stage2 env assignment names do not match the canonical list for aarch64-apple-darwin
  unexpected: SIMPLE_NATIVE_INCREMENTAL
```

PR #674 forwards the variable but `bootstrap_stage3_stage2_canonical_env_names`
was not extended, so the two disagree. Drop the variable to run the lane.

**FIXED** — `bootstrap_stage3_stage2_canonical_env_names`
(`scripts/check/lib/bootstrap-stage3/authority.shs`) now conditionally emits
`SIMPLE_NATIVE_INCREMENTAL` immediately after `SIMPLE_FRONTEND_CACHE_DIR`,
gated on `[ -n "${SIMPLE_NATIVE_INCREMENTAL:-}" ]` — the same condition
`bootstrap_run_stage2_native` uses (`${SIMPLE_NATIVE_INCREMENTAL:+...}`) to
decide whether to forward the assignment at all, and at the same position in
the assignment order. This keeps the check fail-closed in both directions: an
unconditional addition would have made every run with the var *unset* fail as
"missing", and leaving it out entirely reproduces this defect for every run
with the var *set*. No other stage-2 env var needed the same treatment — the
`--cache-dir` flag mentioned in the original defect report is a CLI argument
to `native-build`, not part of the `env -i` allowlist this check covers.
Verified without running a bootstrap: `sh
scripts/check/check-stage2-env-canonical-native-incremental.shs` exercises
`bootstrap_stage3_env_assignment_names` /
`bootstrap_stage3_stage2_canonical_env_names` directly for (1) var unset, (2)
`SIMPLE_NATIVE_INCREMENTAL=1` set — the exact regression fixture for this
defect — and (3) an unrelated unknown env name, confirming the allowlist still
rejects it. All three PASS.

### Regression scaffolding added

- `test/01_unit/compiler/codegen/optional_bound_struct_scalar_field_spec.spl`
  — 8 examples, absolute oracle `632`, plus `i32`/`bool`/`f64`/`text` and a
  nested-optional case. Passes on the seed interpreter (pins the semantics).
- `test/01_unit/compiler/codegen/probe_optional_bound_struct_scalar_field.spl`
  — native probe printing one `PASS`/`FAIL` line, built and run by the
  self-hosted lane with the recipe above. Currently PASSes at T1, which is the
  measurement, not a claim that the defect is fixed.

**Status of the underlying defect: still OPEN, and still worked around at the
three #677 call sites** — which were therefore left in place, since reverting
them without a reproduction would re-open a known Stage-2 blocker.

## Reproduction

Host: macOS 15 (Darwin 25.5.0), Apple M4, `aarch64-apple-darwin`, repo at
`origin/main@f38ceb0f804`. The comparator workaround from
`bootstrap_stage3_comparator_rejects_homebrew_symlinked_cmp_on_macos_2026-09-12.md`
is REQUIRED to get this far:

```sh
PATH="/usr/bin:$PATH" BOOTSTRAP_STAGE3_COMPARE_TOOL=/usr/bin/cmp \
SIMPLE_NATIVE_INCREMENTAL=1 SIMPLE_CACHE_SCOPE=bootstrap-r2 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 \
     --full-bootstrap --mode=dynload --jobs=half
```

Timeline (this run): start 12:14:33Z; Rust seed + runtime rebuilt; Stage 1
preserved 12:15Z; `Stage 2: admitted parent -> bootstrap_main.spl`; Stage 2
native build **completed**; failed in Stage 2 sanity at 12:33:13Z. Wall ~18m.

## The failure

`.simple/storage/build/bootstrap/stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-failure.log`:

```
scripts.check.cert.redeploy_gate.fixtures.hello_world
native-capsule-receipt-invalid
receipt-content-mismatch:expected-bytes=1648:actual-bytes=1648
[native-compile-failed] scripts.check.cert.redeploy_gate.fixtures.hello_world:
  native-capsule-receipt-invalid:...:receipt-content-mismatch:expected-bytes=1648:actual-bytes=1648
===== build outcome summary =====
OK=0  ERROR=1  CRASHED=0  TERMINATED=0
```

The load-bearing detail: **`expected-bytes` and `actual-bytes` are the same
number, 1648.** A receipt-content comparison is rejecting two payloads of
identical length, so this is a content/ordering/encoding difference, not a
truncated or short write — and the error text as written ("content-mismatch"
followed by two equal byte counts) gives an operator nothing to act on. The
message should carry the first differing offset and the two bytes there.

The surrounding harness behaved correctly and is not at fault:
`PASS — 1 check(s), stage stage2 failed (exit 2) and said why`.

## The SEGV did not reproduce

`doc/03_plan/infra/macos_open_bugs_fix_lanes_round2_2026-09-12.md` carries
"Stage 2 `serialize_mir_function` SEGV" as OPEN/unverified since 09-06, with
the instruction to reproduce or retire it. This run is the reproduction attempt:

- Stage 2's native build **completed**; the failure is in the sanity step after it.
- The failing unit exited **rc=1**, not 139/134.
- The build summary reports `CRASHED=0 TERMINATED=0`.
- No `serialize_mir_function`, `Segmentation fault` or `SIGSEGV` string appears
  anywhere under `.simple/storage/build/bootstrap/logs/aarch64-apple-darwin/`.

So on this host, at this commit, Stage 2 does not SEGV. Retiring the SEGV item
outright is not justified from one run (it may be input- or cache-state
dependent), but it should be re-classed from "the remaining Stage-2 blocker" to
"not observed 2026-09-12; blocked behind two other defects", and the capsule
receipt mismatch above is what a Stage-2 lane should work on next.

## Note on where the artifacts landed

The lane was asked to keep artifacts under `build/bootstrap-r2/`. The bootstrap
script writes its own output root and ignored that: everything is under
`.simple/storage/build/bootstrap/`. Only the driver logs
(`build/bootstrap-r2/*.log`) and the launch wrapper are in the requested place.
The `[native-incremental] N reused / M rebuilt` receipt is NOT in the driver
log; it belongs in `.simple/storage/build/bootstrap/logs/<triple>/stage2-native-build.log`
and was absent from this run's copy of it.

## Seed reuse measurement (lane-1 item 4)

The 18m35s cold Rust seed floor is reducible without any new cache: the
digest-keyed store already exists as
`src/compiler_rust/target/bootstrap.generations/<digest>`, it is simply inside
a per-worktree cargo target dir. `cp -Rc` of an existing checkout's
`src/compiler_rust/target` into a fresh worktree (APFS clone, seconds, no extra
space) took the seed build to ~11 min on the first run, and a second run in the
same worktree reused it in **35 s**. No new script is needed; what is missing is
a documented shared-target path. Do NOT symlink the target dir.

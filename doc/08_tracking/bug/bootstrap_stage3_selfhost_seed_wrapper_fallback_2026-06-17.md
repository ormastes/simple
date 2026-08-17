# Bootstrap Stage 3 self-host fails — stage2 `bootstrap_main` binary can only emit a seed-wrapper, not real native code

- **Id:** bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** P2 — **NEEDS REVISIT (2026-06-21):** the parenthetical below
  claims "the seed-built artifacts are valid," but that assumption is now
  contradicted. A fresh `--pure-simple` Stage 4 binary **SIGSEGVs on every
  invocation** (even `print(1)`, both interpret and JIT) via infinite recursion
  in `io.cli_ops.get_args` — see
  `doc/08_tracking/bug/bootstrap_stage4_get_args_infinite_recursion_coredump_2026-06-21.md`.
  If the seed-built fallback artifact is not runnable, this is a
  runtime-correctness regression and likely warrants a P1 bump (or splitting the
  not-runnable-binary symptom into the new bug and keeping this one scoped to the
  self-host-verification gap). Re-triage before closing.
  <br>(original P2 rationale: self-host verification is skipped on every full
  bootstrap; Stage 4 silently falls back to the Rust seed, so the produced
  `build/bootstrap/full/<triple>/simple` is never the self-hosted compiler. The
  reproducible-build guarantee — stage2 SHA256 == stage3 SHA256 — cannot be
  checked. Not a runtime-correctness bug; the seed-built artifacts are valid.)
- **Found:** 2026-06-17 (full-bootstrap regression verification for the JIT
  composite extern-return fix, commit `49ca9697987`; reproduced across two
  consecutive `scripts/bootstrap/bootstrap-from-scratch.sh` runs)
- **Component:** bootstrap pipeline / self-hosted native-build
  (`bootstrap_main.spl`, `native-build` lowering/codegen, cranelift backend)
- **Files:**
  - `scripts/bootstrap/bootstrap-from-scratch.sh` (Stage 3 driver + warning text)
  - `src/app/cli/bootstrap_main.spl` (minimal CLI entry used for stage2/stage3)
  - `build/bootstrap/logs/<triple>/stage3-native-build.log`

## UPDATE 2026-06-26 (LLVM bootstrap — stage4 now partially functional)

The "LLVM 18 absent" precondition was itself a **platform-detection bug**, now
fixed (`scripts/setup/platform-detect.shs`, commit `92e4958`): the bootstrap
only probed the macOS Homebrew path and fell back to cranelift on Linux despite
`/usr/lib/llvm-18` being installed. After rebuilding the Rust seed with
`--features llvm` (stable, no `f128` error, ~3m32s) and running a full LLVM
bootstrap:

- **Stage 3 still fails** the same structural way — stage2 is built from
  `bootstrap_main.spl` (minimal entry, no real lowering/codegen) so the
  self-host step hits the seed-wrapper-fallback guard. The llvm-lib backend
  never engages: Stage 2 is hardcoded cranelift, Stage 3 runs the broken stage2,
  Stage 4 falls back to seed+cranelift.
- **Stage 4 (`build/bootstrap/full/<triple>/simple`) is now PARTIALLY
  FUNCTIONAL — and no longer SIGSEGVs** (contrast the 2026-06-21 NEEDS-REVISIT
  note above):
  - `test` works with **full parity** vs the Rust seed:
    `parsers_json_core` 90/0, `yaml_coverage` 125/0, `json_coverage` 187/0,
    `parsers_sdn_coverage` 78/1. `lint`, `fmt --check`, `--version` also work.
  - `run`, `-c`, and `build` (self-hosted native-build) are **broken**:
    `-c 'print(1+1)'` exits **248** (3/3), `run main.spl` is a silent no-op
    (rc 0, no output), `build` produces no binary. Root cause is the
    **574 stubbed cross-module symbols** the seed's cranelift native-build emits
    when compiling the full compiler (`Generating 574 stub functions for
    unresolved symbols`: `*__ParserModule` per-module symbols, `*_dot_*` method
    symbols, `Dict`, `alloc`, SPIR-V `builder_emit_*`, …). Those symbols are
    only on the execute/codegen paths, which is why `test`/`lint`/`fmt` (intact
    interpreter/analysis paths) pass while `run`/`-c`/`build` fail.

**Consequence for tooling:** the stage4 binary is a usable, parity-verified
**pure-Simple test runner** (so bug fixes can be verified on it), but it must
**not** replace the global `bin/simple` yet — `run`/`-c`/`build` would break.
The blocking fix is twofold: (1) build Stage 2 from the full driver
(`main.spl`, not `bootstrap_main.spl`) so it has real codegen and can self-host;
(2) close the seed native-build's 574-symbol cross-module resolution gap (see
`interp_aot_source_pipeline_stubbed_non_functional_2026-06-25`,
`native_codegen_crossmodule_generic_result_u8_erasure_2026-06-22`).

## OBSERVED

A full bootstrap (cranelift backend, LLVM 18 absent) runs the manual pipeline
`seed → bootstrap_main → bootstrap_main`. Stage 3 (the self-host step:
stage2 binary recompiles `bootstrap_main.spl`) fails with exit 1, and the
pipeline falls back to the Rust seed for Stage 4:

```
Stage 3: stage2 → bootstrap_main.spl (self-host)
  warning: stage3 self-host failed (exit 1); using seed for stage 4
Stage 3 unavailable — using seed for stage 4
Stage 4: compiling full CLI (main.spl) with bootstrap compiler...
```

The proximate error in `stage3-native-build.log` is **not** an LLVM symbol
conflict — it is a guard refusing to emit a seed-wrapper:

```
error: bootstrap_main cannot emit a seed-wrapper fallback for build/bootstrap/stage3/<triple>/simple
error: rebuild with the full Simple driver so native-build uses real Simple lowering/codegen
```

The final bootstrap warning attributes the failure to **LIM-010 (LLVM symbol
conflicts)** per `doc/09_report/bootstrap_crash_report_2026_04_01.md`:

```
WARNING: Bootstrap produced a binary but self-host verification (stage 3) failed.
  The stage2 binary cannot yet recompile itself (LIM-010: LLVM symbol conflicts).
  Stage 4 used the Rust seed instead of the self-hosted compiler.
```

## ROOT CAUSE (proximate)

The Stage 2 binary is compiled from `bootstrap_main.spl` — the **minimal** CLI
entry. That binary does not carry the full Simple native lowering/codegen path,
so when asked to `native-build` itself in Stage 3 it can only produce a
*seed-wrapper fallback* (a thin shim that re-invokes the seed) rather than a real
native binary. A guard in the native-build path rejects the seed-wrapper for the
stage3 output and exits 1.

This is distinct from LIM-010 (the historical LLVM-CommandLine-option /
static-constructor conflict at self-hosted-binary startup). The script's warning
text conflates the two: the *current* proximate cause is the seed-wrapper guard
on the minimal `bootstrap_main` entry, regardless of backend.

## REGRESSION NOTE

`doc/09_report/bootstrap_crash_report_2026_04_01.md` records a state where Stage 3
self-host **worked and was SHA256-reproducible**:

```
Stage 3: stage2 → bootstrap_main.spl   ✓ (100 files, 0.8s compile — SELF-HOST WORKS)
  stage2 SHA256 == stage3 SHA256        ✓ (REPRODUCIBLE BUILD)
```

As of 2026-06-17 that no longer holds on `main` (cranelift path). Whether stage3
ever succeeds again depends on `bootstrap_main.spl` gaining the real
lowering/codegen path (or stage2/stage3 being built from the full driver entry).

## REPRODUCTION

```bash
sh scripts/bootstrap/bootstrap-from-scratch.sh
# inspect:
cat build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log
```

Deterministic: two back-to-back runs on 2026-06-17 produced byte-identical stage
progression; the second skipped the cargo rebuild via input-content-hash match,
confirming the failure is independent of any Rust-seed source change.

## IMPACT / WORKAROUND

- ~~The bootstrap still produces working binaries (Stage 4 uses the seed, which is
  a correct compiler). Runtime correctness is unaffected.~~
  **CONTRADICTED 2026-06-21:** a fresh `--pure-simple` Stage 4 binary is NOT
  runnable — it SIGSEGVs on every invocation via `io.cli_ops.get_args` infinite
  recursion (see
  `doc/08_tracking/bug/bootstrap_stage4_get_args_infinite_recursion_coredump_2026-06-21.md`).
  Treat "Stage 4 fallback produces a working binary" as unverified; re-triage
  severity (see header).
- The lost guarantee is **self-host verification** (stage2 == stage3 SHA256) and
  shipping a genuinely self-hosted `build/bootstrap/full/<triple>/simple`.
- No source-side workaround; it is a pipeline/entry-capability gap.

## PROPOSED FIX OPTIONS (hypotheses — verify against actual native-build path)

1. Build stage2/stage3 from the **full driver entry** (`src/app/cli/main.spl`)
   instead of `bootstrap_main.spl`, so the self-host binary carries real
   native lowering/codegen and can emit a true native artifact.
2. Add the missing native lowering/codegen path to `bootstrap_main.spl` so the
   minimal entry can `native-build` without a seed-wrapper fallback.
3. If self-host is intentionally deferred, make the Stage 3 warning state the
   **actual** proximate cause (seed-wrapper guard on the minimal entry) rather
   than attributing it to LIM-010, to avoid misdiagnosis.

## RELATED

- `doc/09_report/bootstrap_crash_report_2026_04_01.md` (LIM-010 + Stage 3 history)
- `doc/06_spec/test/03_system/compiler/stage3_segfault_fix_spec.md`
- `doc/08_tracking/bug/selfhosted_mcp_binary_segfault_2026-06-02.md`

## 2026-07-24 FONT-VERIFICATION OBSERVATION

A cache-preserving full-driver attempt using the installed `bin/release`
candidate did not converge:

- command entry: `src/app/cli/_CliMain/main_and_help.spl`
- backend/mode: Cranelift, dynload, entry closure, eight requested threads
- cache: `build/bootstrap/native_cache_flat_globals_fixedseed`
  (1,395 objects, 127 MB before and after)
- bound: 600 seconds
- result: exit 124, zero build output, no new cache mtimes, no candidate
- observed worker: one CPU-bound process at about 100% CPU and 73 MB RSS
- retained log:
  `build/native_probe/simple-font-rebuild-20260724.log`

The installed producer identifies itself as Rust-built bootstrap material, so
even a successful first artifact would require a separate-cache stage-2
self-build before it could qualify as pure-Simple evidence. This observation
does not validate the proposed fixes above; it records the current silent,
non-progressing failure mode and prevents font verification from treating the
installed release image as a self-hosted compiler.

## 2026-07-29 Retry 15 Update

The current LLVM path no longer fails at the historical seed-wrapper guard.
Retry 15 produced and admitted a pure-Simple Stage 2 compiler. A direct Stage 3
resume then exposed a different runtime boundary defect:

```text
failed to set environment variable `"SIMPLE_BOOTSTRAP_EXPR_404_S"` to `"\0"`
```

`rt_env_set` converted the byte slice to valid UTF-8 but did not reject an
embedded NUL before calling Rust `std::env::set_var`, which panics on invalid
environment strings. The owner now rejects empty/`=`/NUL keys and NUL values;
`env_set_rejects_invalid_input_without_panicking` executes and passes.

After rebuilding only the affected runtime archives and Stage 2 from retained
caches, Stage 3 cleared the former 5m30s abort and remained CPU-active until its
45-minute cap. It emitted no diagnostic and no final binary; peak RSS was
1,567,392 KiB. This supersedes the old claim that the current proximate failure
is a seed-wrapper fallback. The next evidence action is one Stage 3-only run
with a 90-minute cap, followed by the full-CLI relink only if Stage 3 succeeds.

## Status update 2026-08-01 — NOT YET DONE (still Open)

Pure-Simple self-host is **not complete** at HEAD. Do not close. Progress from
parallel sessions has removed major causes (e.g. `case Some(x)` on nullable `T?`
never matching — `fb1a0033d51`, unresolved names 9,530 → ~195; the `true_*`
prefix-call grammar bug — `28bea12384b`), but Stage 3 / full-CLI self-host is not
green, so the deployed `bin/simple` still lacks `test`/`run`/`lint`.

In parallel, the byte-vs-char / find-as-Option **divergence sweep** continues to
land correctness fixes on `src/**` (waves through 2026-08-01: `4beaa207810`,
`29687ff0d530`, `30fbcdc0f00`). These are independent product-correctness fixes,
not self-host unblockers — the self-host gate remains the umbrella blocker. See
`doc/08_tracking/bug/divergence_byte_char_find_option_sweep_2026-08-01.md` and
`doc/08_tracking/bug/module_lowering_byte_vs_char_sanitizer_2026-08-01.md`.

## 2026-08-17 content re-classification — TITLE IS NOW WRONG; umbrella blocker stays OPEN

Reviewed by the lane owning `src/app/cli/bootstrap_main.spl` and
`src/app/cli/native_build_main.spl`. Classified by CONTENT of current source
(SHA ancestry is unsound in this repo). A bootstrap run was **forbidden this
session** (a live bootstrap owned the host), so nothing about Stage 3 convergence
was re-measured.

### The "seed-wrapper fallback" framing is stale — and the emitted string moved

`bootstrap_main.spl` contains **no** seed-wrapper generation and **no** guard
string. `/usr/bin/grep -rn "seed-wrapper" --include=*.spl --include=*.sh
--include=*.rs .` finds exactly two live sites, neither in `bootstrap_main.spl`:

- `src/compiler/80.driver/driver_bootstrap.spl:103` —
  `CompileResult.CodegenError("bootstrap seed-wrapper fallback was removed")`
- `test/02_integration/os/port/bootstrap_seed_fallback_policy_spec.spl:27,34`

`bootstrap_main.spl` also carries none of the forbidden seed markers
(`compiler_rust`, `execv`, `SIMPLE_BOOTSTRAP_SEED`, `ret i64 0`). Its
`run_native_build_bootstrap` (line 260) routes the Stage4 explicit-entry shape
and the single-`.spl`-positional shape through the **pure-Simple in-process
CompilerDriver**, and asserts a real artifact on the way out:
`file_exists(output)` plus a `<= 300` byte stub rejection (342-348), with the
same contract on the SMF lane (443-450). This matches the 2026-07-29 note above
("The current LLVM path no longer fails at the historical seed-wrapper guard")
and supersedes the title and the ROOT CAUSE section.

The remaining seed delegation is explicit and documented, not a silent fallback:
an `--entry` invocation outside `SIMPLE_BOOTSTRAP_STAGE4=1` calls
`run_rt_native_build` (line 276), i.e. the Rust `rt_native_build` FFI, after
printing a note when `--source` is absent.

Proposed fix option 3 above (restate the Stage 3 warning instead of blaming
LIM-010) is already **moot**: `/usr/bin/grep -rn "LIM-010" scripts/` returns no
matches, so the misattributing warning text no longer exists in the bootstrap
script.

### Live finding: the existing regression spec asserts a string that is gone

`test/02_integration/os/port/bootstrap_seed_fallback_policy_spec.spl:27` still
asserts

```
expect(src).to_contain("bootstrap_main cannot emit a seed-wrapper fallback")
```

against `src/app/cli/bootstrap_main.spl`, which no longer contains that text.
That example is therefore RED for a stale reason, not a real regression — the
guard string it is pinning migrated into `driver_bootstrap.spl` (already covered
by the *next* example in the same spec, line 34). The assertion should be
retargeted or dropped; it is left untouched here because rewriting an assertion
to make it pass is exactly what the testing rules forbid without the finding
being recorded first. Recorded now.

Replacement coverage that does hold at tip:
`test/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.spl`, examples
"keeps bootstrap_main free of seed-wrapper artifact generation", "never reports
in-process native-build success without a real artifact", and "keeps the
cli_mode_text override on both in-process compile lanes".

### Status

**STILL OPEN as an umbrella blocker** — pure-Simple Stage 3 self-host is not
green, and the 2026-08-01 note stands. What is closed is the specific mechanism
in the title: the stage2 binary no longer *has* a seed-wrapper path to fall into.

### What could NOT be proven this session
- Whether Stage 3 converges, times out, or emits a diagnostic. No bootstrap run.
- Whether the stage2 SHA256 == stage3 SHA256 reproducibility check can pass.
- Whether the 574 stubbed cross-module symbols (2026-06-26 note) are still
  emitted — that is seed cranelift native-build, another lane's path.
- Whether the Stage 4 `get_args` infinite-recursion SIGSEGV (2026-06-21) is
  still live; no Stage 4 binary was built or executed.

## 2026-08-17 triage (wave W3) — FAMILY: no source-matched self-hosted binary deployed

This row is one member of a single family, not an independent defect. On this
host `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` is the **Rust
seed**, so every remaining blocker in this row requires building and deploying a
source-matched self-hosted CLI. The rows sharing that blocker are:

- `host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17`
- `stage4_full_cli_source_check_blank_exit8_2026-07-23`
- `self_hosted_cli_native_build_silent_no_artifact_2026-08-14`
- `self_hosted_simpleos_target_native_build_crash_2026-07-11`
- `native_selfhosted_run_segfault_startup_normalize_2026-07-24`
- `bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17`
- `mcp_full_program_native_codegen_and_arg_extract_2026-06-16`
- `no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09` (the family
  statement itself: an ENVIRONMENT fact on this machine, not a code defect)

W3 was explicitly barred from rebuilding or redeploying `bin/simple` /
`bin/release/**` (~16 concurrent lanes share them), so **no execution evidence
for this row was produced or is claimed**. Status is unchanged: OPEN, blocked on
deploy. What W3 did instead was pin, by source spec, the fail-closed checks these
rows depend on, so they cannot be silently lost again while the deploy blocker
persists: `test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl`
(native-build worker exit 0 without an artifact; driver Success without a fresh
staged artifact; argv read through `rt_cli_get_args` rather than a same-named
import). Ablation-verified: neutralising the native_build_main.spl guard takes
that spec from `Results: 3 total, 3 passed` to `3 total, 2 passed, 1 failed`.


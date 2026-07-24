# Bootstrap Stage 3 self-host fails — stage2 `bootstrap_main` binary can only emit a seed-wrapper, not real native code

- **Id:** bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17
- **Status:** Open
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

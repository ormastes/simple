# native-build can report success for a function-less artifact (status: DRIVER GATE LANDED 2026-08-17; original artifact still NOT REPRODUCED)

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

- **Filed:** 2026-08-10
- **Binary measured:** `bin/release/x86_64-unknown-linux-gnu/simple`, 181,524,312 bytes,
  mtime 2026-08-10 11:06:25 UTC. `bin/simple --version` prints the Rust-seed
  warning banner, so this is the **seed**, not a self-hosted binary.
- **Oracle used:** `readelf -sW` symbol-type census on the emitted artifact plus the
  `rc=` line captured from the command under test (never from a pipe).

## Observation under investigation

A `native-build` of `src/os/kernel/arch/x86_64/cstart.spl` was reported to have
emitted an 11 KB artifact whose symbol table held **294 `FILE` symbols and zero
`FUNC` symbols**, while the lane reported `Build complete`. A binary with no
defined function has no `main`/`_start` body: it cannot be a successful build.

## What was reproduced

| lane | invocation | result |
|------|-----------|--------|
| hosted pure-Simple, **good program** (positive control) | `native-build good.spl -o good.out` | `rc=0`, 23,760 B, **77 `FUNC`** — correct |
| hosted pure-Simple, syntactically bad program | `native-build bad.spl -o bad.out` | `rc=1`, `error: HIR lowering error ...`, **no artifact** — correct |
| cross-target Rust handler | `native-build --target x86_64-unknown-simpleos --entry .../cstart.spl` | `rc=1`, `ld.lld: error: undefined symbol: rt_*` (12+), **no artifact** — correct |

So on the three lanes measured, a failed compile did **not** produce a
false success. The `0-FUNC + Build complete` combination was **not reproduced**
in this session and is left OPEN rather than asserted as a defect.

## The real structural hole (confirmed by reading, not by reproduction)

`src/app/io/_CliCompile/compile_targets.spl:1239` is the single funnel every
pure-Simple `native-build` success passes through. Its guard is:

```
if not _cli_file_exists_impl(staged_output):
    ... "error: native-build reported success but produced no fresh output binary"
```

It checks that the artifact **exists**. It does not check that the artifact
contains anything. An 11 KB ELF with 294 `FILE` symbols and 0 `FUNC` symbols
satisfies this guard exactly and is published and reported as a success. The
same shape exists in the Rust handler
(`src/compiler_rust/driver/src/cli/native_build.rs:626-660`), which prints
`Build complete: {compiled} compiled, {cached} cached, {failed} failed` and
returns `0` unconditionally on `Ok`; the `if result.failed > 0` warning at
:656 is currently unreachable because
`compiler/src/pipeline/native_project/mod.rs:996-1008` converts any failure
into `Err` first.

## Mitigation landed

`scripts/check/check-native-build-artifact-has-functions.shs` — reads the
artifact and fails when an ELF with a `.symtab` carries zero defined `FUNC`
symbols. Fail-closed on every "cannot tell" case (no args, missing file,
stripped, non-ELF → `ERROR`, never a vacuous `PASS`). `--selftest` runs before
every scan and is fatal: it assembles a real 1-`FUNC` ELF and a real 0-`FUNC`
ELF and requires accept/reject respectively, so the gate proves its own
negative control on every invocation.

**Placement argument (gate, not driver).** The natural home looks like the
funnel above, and a pure-Simple ELF reader already exists
(`src/compiler/70.backend/introspection/elf_symbols.spl`). It was deliberately
NOT wired in: `file_read_bytes` returns `[i64]`, so the funnel would have to
materialise the whole artifact as a boxed array on the hot bootstrap path —
for the ~180 MB stage-2/3 compiler binary that is an unbounded cost paid inside
the *interpreted* native-build worker, i.e. a guaranteed perf regression on the
build everyone runs. `readelf` is already a hard dependency of this toolchain
(the link step shells out to `ld.lld`), so the gate pays O(symtab) in C instead
of O(file) in interpreted Simple. The correct in-driver fix is to have codegen
report its emitted-function count directly rather than re-parse its own output;
that is left as the follow-up below.

## Follow-up (not done)

- Have the driver assert a nonzero emitted-function count from codegen state
  (no artifact re-parse) at `compile_targets.spl:1239`, and make it the funnel
  condition alongside the existence check.
- Re-verify the lanes below, which use `native-build` exit code as their sole
  oracle with no artifact inspection and no execution of the result. Enumerated,
  not re-verified here (heuristic classification: no `nm`/`readelf`/`FUNC` check
  and no run of the produced binary):
  `check-build-defaults-collect-all-and-incremental.shs`,
  `check-cranelift-aot-aggregates.shs`, `check-engine-differential.shs`,
  `check-link-native-build-parity.shs`, `check-native-consecutive-zero-arg-receiver.shs`,
  `check-native-enum-match-payload.shs`, `check-native-field-text-receiver.shs`,
  `check-native-immutable-fn-receiver.shs`, `check-native-utf8-slice.shs`,
  `check-processing-fill-wire-copy.shs`, `check-process-parent-death.shs`,
  `check-seed-extern-registry.shs`, `check-tuple-index-out-of-range.shs`,
  `check-u32-array-not-packed.shs`, `check-heavy-work-preflight.shs`,
  `cert/redeploy_gate/candidate_frontend_admission.shs`,
  `lib/bootstrap-stage3/manifest-verify.shs`,
  `build-simpleos-arm64-desktop-engine2d-attested.shs`,
  `build-x25519mlkem768-gpu-evidence-runner.shs`,
  `check-macos-metal-browser-backing-evidence.shs`,
  `check-production-gui-web-host-gpu-queue-readback-evidence.shs`,
  `check-rocm-engine2d-font-readback.shs`,
  `check-simpleos-usb-xhci-qemu.shs`, `check-simpleos-wm-host-seam-evidence.shs`,
  `check-simpleos-wm-visible-display-evidence.shs`, `sync-native-health-guard.shs`.
  Lanes that DO execute the produced binary (e.g. `check-aot-smoke.shs`,
  `check-native-print-stdout-oracle.shs`) are not suspect: running a 0-`FUNC`
  artifact cannot pass.


---

## Driver-side gate landed (2026-08-17)

The follow-up this doc listed as "not done" — *have the driver assert a nonzero
emitted-function count ... and make it the funnel condition alongside the
existence check* — is now closed on the Rust handler, without re-parsing the
artifact.

`src/compiler_rust/driver/src/cli/native_build.rs`, in the `Ok(result)` arm,
used to end in an unconditional `0`. Two vacuous-success paths are now
fail-closed:

1. **`result.failed > 0` used to print `Warning: N files failed to compile` and
   then return 0.** This doc argued it was unreachable because
   `pipeline/native_project/mod.rs:996-1008` converts failures into `Err`
   first. That is a claim about today's code, not an invariant this function can
   check, and the cost of being wrong is a build that lies. It now prints
   `error: native-build produced an artifact but N file(s) failed to compile —
   refusing to report success` and returns 1.
2. **`compiled == 0 && cached == 0` now returns 1.** No module contributed any
   code, so the artifact cannot hold a function body — exactly the
   `0-FUNC + Build complete` shape. A fully-cached incremental rebuild has
   `cached > 0` and an archive build has `compiled > 0`, so neither is caught.

This is the same defect class as `TestRunResult::success()` being
`total_failed == 0`: a process reporting success while its own accounting says
it produced nothing.

**Honest limits — what this does NOT prove.**

- **The originally observed artifact still does not reproduce.** As recorded
  above, all three measured lanes behaved correctly. The gate is a fail-closed
  invariant, not a demonstrated fix for a demonstrated failure. `failed > 0` in
  particular remains, as far as could be determined by reading, unreachable —
  the change makes it safe rather than fixing an observed bug.
- **The pure-Simple funnel at `src/app/io/_CliCompile/compile_targets.spl:1239`
  is UNCHANGED.** It still checks only that the artifact exists. The argument in
  this doc against wiring an interpreted ELF reader into that hot bootstrap path
  still holds and was not revisited. The pure-Simple lane is therefore still
  covered only by the external `scripts/check/` gate, not in-driver.
- The gate was compiled (`cargo build --release --bin simple`, clean) but was
  not exercised against a real functionless build, because no way to produce one
  was found.

## Artifacts

- Similar-problem detection spec (subprocess-based; an in-process example cannot
  reach codegen at all):
  `test/01_unit/compiler/driver/native_build_success_implies_functions_spec.spl`.
  It pins the INVARIANT the observation violated — `native-build exit 0 ==> the
  artifact defines >= 1 FUNC symbol` — measured with `readelf -sW`, plus a
  program shape carrying live, called and dead functions so a fix that
  special-cases one shape does not satisfy it. Its second example invokes
  `check-native-build-artifact-has-functions.shs --selftest` and asserts the
  literal `0-FUNC rejected` text, so the gate's negative control cannot be
  gutted without this spec going red.


## 2026-08-17 CORE-P1 triage: STILL PRESENT in current source

Re-verified against CURRENT SOURCE during the crit_01 CORE-P1 sweep. Confirmed still present -- the false-green is unguarded on the emit path. `src/compiler_rust/driver/src/cli/native_build.rs:640-673` is `Ok(result) => { println!("Build complete: ..."); ... 0 }`: it returns 0 unconditionally and prints only `binary_size`, with NO function/symbol-count assertion. The `if result.failed > 0` branch is a warning only, and is unreachable anyway because the pipeline converts failures into `Err`. The only existing check, `scripts/check/check-native-build-artifact-has-functions.shs`, is an external script that nothing on the emit path invokes -- so an artifact with zero emitted functions still exits success.

## 2026-08-18 — DRIVER-SIDE FAIL-CLOSED GATE LANDED (Rust `native-build` handler)

The follow-up above ("have the driver assert a nonzero emitted-function count
... alongside the existence check") is now done on the **Rust** handler.
`src/compiler_rust/driver/src/cli/native_build.rs` no longer returns `0`
unconditionally on `Ok(result)`. Three independent fail-closed conditions,
each of which previously reported SUCCESS:

1. **`result.failed > 0`** — was only `eprintln!("Warning: ...")` followed by
   `0`. Now returns `1`.
2. **Artifact missing / empty / function-less** — new
   `verify_emitted_artifact()`. For an ELF64 LE image it walks the section
   headers and counts symbols with `STT_FUNC` and `st_shndx != SHN_UNDEF`
   across `.symtab`/`.dynsym`, rejecting an image whose symbol table exists
   and carries **zero** defined `FUNC` symbols — exactly the `294 FILE /
   0 FUNC` shape of the original observation. A stripped image (no `.symtab`)
   falls back to requiring a non-empty `.text`. Non-ELF outputs (`.a`, wasm,
   mach-o, ELF32) are checked only for non-emptiness, which is all that can
   honestly be claimed about them.
3. **Stale artifact left by a previous run** — the nastiest member of the
   family, because a leftover file makes any existence check pass. When a link
   step actually ran (`result.link_time > 0`) the artifact's mtime must be at
   or after the build's start (2 s slack for coarse fs timestamps). Cached
   builds that ran no link pass `None` and are never failed for not rewriting
   a file they never touched.

**No stub, no empty object and no file is ever fabricated to make a check
pass** — the forbidden shape of `linker/native_binary/stubs.rs:209-221`. The
gate only reads what was emitted.

### Engine

The defect is in the **compiled Rust `native-build` driver** (native/AOT
lane). It is NOT reachable from `bin/simple test` (tree-walk interpreter) or
`run` (Cranelift JIT), so no interpreted spec can exercise it; the tests are
Rust `#[test]`s in the same crate, run by `cargo test -p simple-driver --lib`.

### Evidence

Fixtures are real ELF images built by the host toolchain (`cc`, `ld`) and
cross-checked against two independent oracles: `readelf -sW` (good.out = 8
defined `FUNC`, nofunc.out = 0) and the pre-existing
`scripts/check/check-native-build-artifact-has-functions.shs`, which returns
`PASS — 1 artifact(s) checked ...` rc 0 on good.out and `FAIL — 1 artifact(s)
checked, 1 with zero defined FUNC symbols or missing` rc 1 on nofunc.out —
agreeing with this gate on both. Exit codes read on the line AFTER each
command, never through a pipe.

| fixture | pre-fix driver | post-fix verdict | rc |
|---|---|---|---|
| real binary, fresh | `0` (success) | `OK` | 0 |
| ELF64, symtab, **0 FUNC** | `0` (**false green**) | `REJECT ... zero defined FUNC symbols` | 1 |
| artifact absent | `0` (**false green**) | `REJECT ... does not exist` | 1 |
| artifact empty (0 bytes) | `0` (**false green**) | `REJECT ... is empty` | 1 |
| valid binary, **stale**, link ran | `0` (**false green**) | `REJECT ... is STALE` | 1 |
| valid binary, no link ran (cached) | `0` | `OK` | 0 |

`cargo test -p simple-driver --lib native_build`, run against a pristine
`origin/main` tree materialised by `git archive` (the shared working copy was
concurrently broken by another lane in
`compiler/src/interpreter_state.rs` — E0428/E0592, unrelated to this change):

- **before** (unmodified `origin/main`): `test result: ok. 10 passed` — the
  three gate tests do not exist.
- **after**: `test result: ok. 13 passed; 0 failed`, including
  `rejects_missing_and_empty_artifacts`,
  `accepts_real_binary_and_rejects_functionless_elf` and
  `rejects_stale_artifact_left_by_a_previous_run`. 0 occurrences of `error[E`.

**Negative control.** Reverting the gate removes `verify_emitted_artifact`, so
all three tests fail (compile error) rather than silently passing; and the
reverted `Ok` arm is a literal unconditional `0`, so every row of the table
above returns 0 again.

### Honestly NOT verified

- The original `294 FILE / 0 FUNC` artifact was **still not reproduced
  end-to-end** — as with every prior lane. The gate is proven on constructed
  ELF fixtures of that exact shape, not on a native-build that spontaneously
  produced one.
- No end-to-end `native-build` invocation was run against the patched driver
  (building the ~181 MB `simple` binary is out of budget for this lane and
  `bin/simple` must not be redeployed while a bootstrap is running), so the
  "a good build still exits 0" property is proven only at the function level.
- The **pure-Simple** funnel `src/app/io/_CliCompile/compile_targets.spl:1239`
  still checks existence only; the placement argument above still stands, so
  that half keeps relying on the shell gate. Status stays OPEN for it.

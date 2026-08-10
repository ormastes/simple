# native-build can report success for a function-less artifact (status: PARTIALLY REPRODUCED)

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

# Windows MSVC Stage 2: CompilerConfig/CompileOptions by-value struct transport corrupts fields non-deterministically

**Date:** 2026-08-31
**Status:** CONFIRMED (measured), NOT FIXED — flagged as core-codegen, fix deferred
**Area:** native codegen / LLVM backend, MSVC ABI, struct-by-value return and parameter transport
**Severity:** High — silently corrupts unrelated struct fields at runtime, blocks Windows Stage 2 admission entirely
**Platform:** `x86_64-pc-windows-msvc` native (LLVM 18) build only. Not yet checked on Linux/macOS — see Unix-safety note below.

## Symptom

The Windows MSVC Stage 2 native link now succeeds (108,194,816-byte
`simple.exe`, zero unresolved symbols, runs and answers `--version` cleanly),
but is rejected by the bootstrap sanity gate:

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 unsupported_status=1 frontend_status=1 candidate_unchanged=true
rejected Stage 2 binary preserved:
  build/w/stage2/x86_64-pc-windows-msvc/simple.exe.rejected
```

Reproduced by hand:

```
$ printf 'fn main():\n    print "hi"\n' > /tmp/h.spl
$ simple.exe.rejected compile /tmp/h.spl --format=smf -o /tmp/h.smf
error: in-process SMF compile: MC/DC global byte budget must be at least the owner byte budget
```

## Root message site (verified, sole writer/reader)

`src/compiler/80.driver/driver_types.spl:568` and `:570-573`, in
`CompileContext.create`:

```
if options.mcdc_global_bytes >= compiler_config.mcdc_owner_bytes:
    compiler_config.mcdc_global_bytes = options.mcdc_global_bytes
else:
    config["mcdc_config_error"] = "MC/DC global byte budget must be at least the owner byte budget"
...
if compiler_config.mcdc_global_bytes < compiler_config.mcdc_owner_bytes:
    config["mcdc_config_error"] = "MC/DC global byte budget must be at least the owner byte budget"
```

Confirmed by grep that these are the only two writers of `mcdc_config_error`
in the whole tree, and the sole reader is
`src/compiler/80.driver/driver_orchestration.spl:85-88`, which turns it
straight into the fatal `CodegenError` seen above. No other candidate site
(e.g. the `config["mcdc_global_bytes"] = ...to_text()` / `_driver_mcdc_budget`
dict round-trip read back in `driver_pipeline_lowering.spl:212/238/294`) is
involved — the error never gets that far.

Declared defaults are sane and would never trip this check:
`src/compiler/00.common/config.spl:101-102` — `mcdc_owner_bytes: 1048576`,
`mcdc_global_bytes: 67108864`. No `SIMPLE_MCDC_*` env vars are set in the
repro environment. `run_compile_bootstrap` (the CLI path actually exercised
by `compile --format=smf`, `src/app/cli/bootstrap_main.spl:520-565`) never
sets `options.mcdc_owner_bytes`/`mcdc_global_bytes` at all, and the bootstrap
CLI does not parse `--mcdc-owner-bytes`/`--mcdc-global-bytes` — those flags
are absent from `bootstrap_compile_option_takes_value` and from every
arg-scanning helper in that file. Passing them by hand producing no change in
behavior is explained by this, not by anything downstream; established by
direct code reading, not assumed.

## Measured runtime values (the actual finding)

Added temporary unconditional `print` diagnostics at three points in
`CompileContext.create` (immediately after `CompilerConfig.from_env()`,
immediately after the CLI-override block, and printing the raw
`options.mcdc_*` fields), rebuilt Stage 2 via the sanctioned
`scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap
--stop-after-stage2` pipeline, confirmed the print strings landed in the
resulting binary (`strings simple.exe.rejected | grep DIAG`), then ran the
exact repro three times against the identical rebuilt binary and input file:

| run | after from_env() (owner / global) | options.* (owner / global / mode_text) | after CLI-apply (owner / global) |
|---|---|---|---|
| 1 | -1 / -1 | 2456074614833 / 1 / "" | 2456074614833 / -1 |
| 2 | -1 / -1 | 2318166374161 / 1 / "" | 2318166374161 / -1 |
| 3 | 8243126012946380655 / 3564137775855134803 | 2270045068145 / 1 / "" | 2270045068145 / 3564137775855134803 |

None of these match the declared defaults (1048576 / 67108864) or the
declared CompileOptions defaults (0 / 0). The values differ between runs of
the byte-identical binary on the byte-identical input — this is the
load-bearing observation. A fixed logic bug (wrong comparison operator, an
off-by-one field read, a bad literal lowering of 67108864) would reproduce
the same wrong value every run. Run-to-run variation, including values that
look like heap/stack addresses (~0x23'xxxx'xxxx, plausible Windows heap
address magnitudes) and a run producing near-random full-range u64 garbage
(8243126012946380655), is the signature of reading uninitialized or
corrupted memory, not of a deterministic mistranslation.

Two sub-observations, both consistent across all 3 runs and worth recording
precisely rather than only asserting "it's random":

- `compiler_config.{owner,global}` are already wrong immediately after
  `CompilerConfig.from_env()` returns — before `options` is consulted at
  all. Since no env vars are set, `from_env()` should be a pure passthrough
  of `CompilerConfig.default()`'s literal 1048576/67108864. The corruption
  is therefore present in the struct-by-value return of
  `CompilerConfig.default()`/`from_env()` itself (`config.spl:92-141`), not
  merely in `CompileOptions` transport.
- `options.mcdc_global_bytes` reads as 1 in all three runs (not random),
  while `options.mcdc_owner_bytes` reads as a different large/address-like
  value each run. This is consistent with the 47-field `CompileOptions`
  aggregate (passed by value into `create(options: CompileOptions)`, per the
  existing comment at `driver_compile_options.spl:120-124`, "Standalone
  bootstrap binaries have historically corrupted tail fields of large
  by-value aggregates") misreading a different, nearby field's value for the
  global_bytes slot (candidate: `bootstrap_input_count`, which
  `run_compile_bootstrap` explicitly sets to 1) while the owner_bytes slot
  reads genuinely uninitialized/stale memory. This is a plausible, but NOT
  independently proven, more specific mechanism — flagged as a lead, not a
  conclusion.

The downstream comparison logic itself is not at fault: given the measured
corrupted inputs, all three runs are internally consistent with the code as
written (verified by hand-tracing each run's four printed numbers through
the two `if` blocks to the observed error).

## Verdict on the task hypothesis

CONFIRMED, and broader than originally suspected. The original hypothesis was
"native codegen not materializing CompilerConfig's declared struct-field
defaults." The measured evidence shows something more general: the by-value
transport of at least two different struct types (CompilerConfig via
from_env()'s return, and CompileOptions via the create(options: ...)
parameter) both exhibit field corruption on this Windows MSVC LLVM build, and
the corruption is non-deterministic (varies run-to-run), which is a stronger
and more alarming claim than "defaults silently read as zero." This is
consistent with, and likely the same defect class as, the already-tracked
"tail fields of large by-value aggregates" note in
`driver_compile_options.spl:120-124` and the Cranelift-side
`doc/08_tracking/bug/stage3_freestanding_struct_by_value_corrupts_pmm_2026-07-11.md`
— both prior sightings of struct-by-value ABI corruption in this compiler, on
different backends/targets. This is the first sighting specifically on the
Windows MSVC LLVM backend for a normal (non-freestanding) struct return and
parameter, i.e. the most "ordinary" code path yet shown to trip it.

## Why this was NOT fixed here

Per task instructions: a general struct-default/struct-by-value-transport
codegen defect is core codegen. A speculative fix at the driver_types.spl
call site (e.g. re-deriving mcdc_owner_bytes/mcdc_global_bytes through a
scalar save/restore idiom, mirroring
compileoptions_normalize_mir_optimization's existing workaround for
CompileOptions) would silence this symptom without addressing the underlying
corruption, which can affect any other struct field in the compiler that
relies on a by-value return or a by-value struct parameter on this target —
including ones with no existing symptom to notice by. The temporary
diagnostic print statements have been reverted
(`git checkout -- src/compiler/80.driver/driver_types.spl`); this repo is
otherwise unchanged by this investigation.

## Repro (for the next session)

```bash
# from repo root, MSVC env sourced as in run_s2final.sh
sh scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap \
  --stop-after-stage2 --output=build/w
printf 'fn main():\n    print "hi"\n' > /tmp/h.spl
./build/w/stage2/x86_64-pc-windows-msvc/simple.exe.rejected \
  compile /tmp/h.spl --format=smf -o /tmp/h.smf
# rc=1, "MC/DC global byte budget must be at least the owner byte budget"
# Run 3x back-to-back with the SAME binary+input to see the values change.
```

## Unix-safety note

No source was changed by this investigation (diagnostic prints added and then
reverted), so there is zero behavior change on Linux/macOS or any other
target. Whether the same by-value-transport corruption reproduces on
Linux/macOS x86_64-unknown-linux-gnu or aarch64-apple-darwin native builds is
UNKNOWN and not tested here — worth a follow-up probe, since a defect this
general in the shared LLVM backend plausibly is not MSVC-ABI-specific, though
the two prior sightings referenced above (this repo's Cranelift freestanding
case, and the pre-existing CompileOptions "tail field" comment which predates
any Windows-specific work) suggest it may be a general aggregate-ABI issue
rather than something scoped to the MSVC calling convention specifically.

## Suggested next steps (not taken here)

1. Isolate with a minimal standalone repro outside the full driver: a bare
   .spl file with a ~12-field struct (matching CompilerConfig's shape,
   including an enum field, a nested struct field, and a Dict field) whose
   default() returns literal values, compiled and run via
   native-build/compile --format=smf on the same MSVC target, to confirm the
   corruption reproduces without any of the bootstrap/driver machinery in
   the loop, and to isolate which field type (the Dict<text,text> values
   field is a candidate, cf.
   doc/08_tracking/bug/bootstrap_lane_dict_global_uninitialized_alloca_2026-07-27.md
   for a related-but-distinct Dict-lowering defect) is implicated.
2. If confirmed minimal, treat as a P0 native-codegen correctness bug for the
   MSVC lane (or broader) rather than working around it per call site.
3. Only after a real fix lands: re-run this exact repro and confirm the four
   printed values stabilize at 1048576/67108864/0/0 across repeated runs,
   then re-attempt Stage 2 admission.

## Related

- `src/compiler/00.common/driver_compile_options.spl:120-124` (pre-existing
  "tail fields of large by-value aggregates" comment and workaround)
- `src/app/cli/bootstrap_main.spl:428-435` (documents options.mode enum not
  surviving struct transport into a compiled Stage 2 driver — same class)
- `doc/08_tracking/bug/stage3_freestanding_struct_by_value_corrupts_pmm_2026-07-11.md`
- `doc/08_tracking/bug/bootstrap_lane_dict_global_uninitialized_alloca_2026-07-27.md`
- `doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`

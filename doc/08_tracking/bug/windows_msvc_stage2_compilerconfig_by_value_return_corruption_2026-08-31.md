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

## 2026-08-31 follow-up: minimal-repro attempt + analytical mechanism lead (NOT fixed, NOT independently reproduced)

Goal for this session: build a minimal standalone `.spl` repro outside the
full driver/bootstrap machinery (per "Suggested next steps" #1 above), isolate
the trigger axis, and locate the mechanism.

### Minimal repro: blocked by unrelated toolchain defects (all newly found, all real)

Attempted to use the already-built Rust seed
(`src/compiler_rust/target/bootstrap/simple.exe`) to `native-build`/`compile
--native` small `.spl` fixtures directly, bypassing the full bootstrap
pipeline. Could not get a working native-build+run cycle in this session.
Three independent blockers hit, in order:

1. `SIMPLE_RUNTIME_PATH` bundle detection requires both runtime libs in ONE
   directory, but the seed's own build splits them.
   `NativeBinaryBuilder::has_target_runtime_bundle`
   (`compiler/src/linker/native_binary/builder.rs:20-28`) only accepts a
   bundle when `simple_runtime.lib` AND `simple_native_all.lib` both exist in
   the same `library_paths` entry. The seed's own cargo build puts them in
   different directories: `target/bootstrap/deps/simple_runtime.lib` vs.
   `target/bootstrap/simple_native_all.lib`. With `--target
   x86_64-pc-windows-msvc --native` and `SIMPLE_RUNTIME_PATH` pointed at
   `target/bootstrap`, this fails with "missing target runtime/sysroot ...".
   Workaround: copy `deps/simple_runtime.lib` next to
   `simple_native_all.lib`; then the runtime-bundle check passes.
2. With the bundle fixed, `--target x86_64-pc-windows-msvc` produces a
   linker-flavor/executable mismatch that was NOT the struct-ABI bug. The
   final link step invokes `lld-link.exe` (the MSVC-mode LLD front end) but
   feeds it GNU-style argv (`-o`, `-L`, `-Bstatic`, `-lsimple_runtime`,
   `-Bdynamic`, `-lc`, `-lmsvcrt`, ...): `lld-link` logs "ignoring unknown
   argument" for every one of them and then fails to open the output path.
   This happened with `SIMPLE_LINKER_FLAVOR=msvc` and `SIMPLE_WINDOWS_ABI=msvc`
   both exported, which per `Target::linker_flavor()`
   (`common/src/target.rs:772-800`) should force `LinkerFlavor::Msvc`, and an
   explicit `--target ...-msvc` also sets `linker_flavor_hint =
   Some(Msvc)` via `from_triple` (`common/src/target.rs:661-668`) — so
   `LinkerFlavor::Msvc` should have been selected either way. Did not
   root-cause which code path actually decided to emit GNU-style tokens
   (candidates: `linker/builder.rs:214 fn link`, or the argv assembly in
   `native_binary/linker.rs` upstream of the two `match linker_flavor` arms
   at lines 180 and 211, which only special-case `/WHOLEARCHIVE:` and
   `/FORCE:UNRESOLVED`, not the base `-o`/`-L`/`-l` tokens). This is a
   genuine, separate, reproducible defect in the ad hoc `compile --native
   --target=x86_64-pc-windows-msvc` CLI path off the Rust seed — worth its
   own bug record — but it is not the struct-corruption bug from the top of
   this doc; it prevents even producing an executable at all, let alone
   running one to observe field corruption.
3. Compiling for host with no `--target` instead auto-selects
   `LinkerFlavor::Gnu` (because `MSYSTEM=MINGW64` is set — see the
   `linker_flavor()` fallback branch), and links with real GNU `ld`
   successfully accepting the argv this time — but the platform default
   library list hardcodes `vec!["c".to_string(), "msvcrt", "kernel32", ...]`
   for `TargetOS::Windows` regardless of flavor
   (`native_binary/linker.rs:106-109`). MinGW has no `libc.a` (that name is
   MSVC-only; MinGW's libc is `libmsvcrt.a`), so raw `ld` fails with `cannot
   find -lc`. Workaround: copied `mingw64/lib/libmsvcrt.a` to
   `mingw64/lib/libc.a` as a local alias. That cleared the `-lc` error but
   then hit a missing `__main` symbol (MinGW's CRT startup glue, normally
   supplied by the `gcc`/`clang` driver's default objects, absent because the
   compiler invokes raw `ld.exe` directly rather than through a CRT-aware
   driver). Did not chase further.

Net: the sanctioned bootstrap script (`run_s2final.sh` ->
`scripts/bootstrap/bootstrap-windows.sh`) evidently gets all of the above
right end-to-end (it is what produced the working, 108 MB
`simple.exe.rejected`), but none of the ad hoc single-file CLI invocations
attempted here reproduced that success. A real minimal-fixture repro on this
host most likely needs to either fix these three items, or borrow whatever
the bootstrap script does differently rather than inventing a new invocation.

### Re-confirmation (no new repro needed — the existing artifact still trips it on demand)

The rejected Stage 2 binary from the prior session still carries its
diagnostic prints (not reverted from *this* binary, only from source — the
record's own note "temporary diagnostic print statements have been reverted"
refers to the `.spl` source, not this already-built artifact). Every
invocation of it — `compile` or `native-build`, on any input, including a
trivial `fn main(): print "hi"` — prints the same three `DIAG` lines and then
fails on the MC/DC gate before doing anything else:

```
DIAG after from_env: owner=140714796318720 global=140714796487808
DIAG options: owner=2297553734337 global=1 mode_text=
DIAG after cli-apply: owner=2297553734337 global=140714796487808
```

A fourth independent measurement (see the table above for the first three),
again non-repeating and address-shaped (`140714796318720` = `0x7FF9...`
range, a plausible Windows user-mode VA). This confirms the corruption is
unconditional for this binary — it fires on every command, not just `compile
--format=smf` — which was already implied but not stated explicitly in the
original record.

### Analytical mechanism lead (source-reading only — NOT run or verified this session)

Traced how a Simple struct value is represented and copied in the LLVM
backend, looking specifically for a Win64-vs-SysV aggregate-classification
bug (the task's leading hypothesis). Two findings:

1. The calling-convention theory looks wrong for this call. Every struct or
   class value in this backend is represented as a single heap-boxed, tagged
   64-bit pointer ("tagged-value ABI"), never as a real LLVM aggregate
   crossing a call boundary:
   - `create_function_signature` (`compiler/src/codegen/llvm/backend_core.rs:1183-1216`)
     builds a function's LLVM type from `ret_llvm = self.llvm_type(return_type)`
     matched only against `IntType | FloatType | PointerType` —
     `_ => return Err(unsupported_return_type())`. Since compiling the real
     driver (which returns `CompilerConfig` by value from several functions)
     succeeds, `llvm_type()` must already lower every struct return type to
     one of those three, never to a genuine `StructType`.
   - `Terminator::Return(Some(vreg))` (`codegen/llvm/instructions.rs:678-696`)
     unconditionally coerces the return value to `i64` — comment: "All
     functions return i64 in the tagged-value ABI".
   - `compile_struct_init` (`codegen/llvm/functions/objects.rs:14-106`)
     allocates the struct via `rt_alloc` (heap) and returns a tagged pointer
     (`ptr | 1`), never a stack aggregate.

   A value that only ever crosses call boundaries as a single scalar i64
   (pointer or inline bit pattern) is immune to the SysV-vs-Win64
   aggregate-register-classification mismatch the task brief flagged as the
   leading suspect — that class of bug needs a real multi-register/indirect
   aggregate ABI in play, which this internal convention does not have. This
   is evidence against a Win64-ABI-specific explanation for calls that stay
   inside Simple-to-Simple codegen (which `CompilerConfig.from_env()` calling
   into `CompileContext.create()` is) — though it does not rule out the
   Win64 ABI mattering at some other boundary (e.g. a genuine `extern "C"`
   call into a C runtime function, which was not traced this session).

2. Field layout is computed by a self-admittedly wrong, uniform
   8-bytes-per-field formula, with a comment flagging exactly this class of
   risk. `lower_struct_init_expr`
   (`compiler/src/mir/lower/lowering_expr_struct.rs:136-151`) computes each
   field's offset as `field_index * 8`, with its own comment: "For now, use
   simple sequential layout (simplified, may not match actual layout)" /
   "Assume 8-byte fields for simplicity (pointer-sized)". The struct-field
   READ path, `lower_field_access_expr` (same file, `byte_offset =
   (field_index as u32) * 8` at line ~326), uses the identical formula, so
   within this one file reads and writes are self-consistent — no read/write
   mismatch was found inside `lowering_expr_struct.rs` itself. However, both
   offset computations carry the comment "Native-project lowering replaces
   this with an authoritative collision-free module-qualified layout
   decision" (referring to `pipeline/native_project/compiler.rs:1697 fn
   qualify_native_struct_layouts`) — tracing that function shows it patches
   only `owner_has_vtable` (a bool), not the byte offsets themselves. So for
   a native build, offsets stay on the naive per-field-index formula
   everywhere traced this session. A third offset-computation site (e.g.
   `self.field` access inside an `impl CompilerConfig:` method body, which
   may lower through different code than `lower_field_access_expr`) was not
   found but also not ruled out — that is the most promising untraced lead
   for a future session with a working repro loop.
3. `rt_alloc` zero-initializes (`calloc`), which refutes the simplest
   "truncated copy leaves stale/uninitialized tail bytes" theory. `rt_alloc`
   (`src/runtime/runtime_memory.c:265-291`, all three paths:
   guarded/hardened/plain) allocates via `calloc`. A struct copy that wrote
   fewer words than it should would read back as zero in the missing slots,
   not as the address-shaped garbage actually measured (`2456074614833`,
   `140714796318720`, etc. — all in plausible Windows heap/stack VA ranges).
   This favors a field-slot misalignment theory (some field's real, valid
   pointer-shaped payload landing in a different field's slot) over an
   "uninitialized memory" theory, and is consistent with heap-address-shaped
   values differing per run simply because heap addresses themselves vary
   run to run (ASLR / allocator state) even when the underlying bug is fully
   deterministic in which slot gets which field's value.

### Windows-specific vs. general: still unresolved, same as the original record

Every file read this session (`codegen/llvm/**`,
`mir/lower/lowering_expr_struct.rs`, `pipeline/native_project/compiler.rs`,
`runtime/runtime_memory.c`) is shared across every LLVM target — no
`#[cfg(target_os = "windows")]` or triple-string branching was found in any
of the mechanisms traced above. If the field-layout-mismatch lead above is
the actual cause, it would most likely be a general defect, not
Windows/MSVC-specific — but, as with the original record, this is inferred
from reading code, not measured on a second platform, and this session had
no means to run a Linux/macOS build to check.

### What was NOT done

No source files were changed. No fix was attempted (per task guidance: a
broad/uncertain core-codegen change should stop at diagnosis). The two new
`.spl` fixtures written this session (`repro/t0_hello.spl`,
`repro/r1_struct2.spl`) never successfully compiled to a runnable native
binary due to the toolchain blockers above, so they produced no new
empirical data point beyond the re-confirmation above.

### Recommended next steps (revised)

1. Fix the toolchain blockers above first (co-locate the two runtime `.lib`
   files or fix `has_target_runtime_bundle`'s single-directory assumption;
   root-cause the `lld-link.exe`-vs-GNU-argv mismatch for explicit `--target
   x86_64-pc-windows-msvc` builds) so a real edit-compile-run loop is
   possible on this host without going through the ~5-minute full bootstrap
   each time.
2. Once that loop works, instrument `compile_struct_init` and
   `compile_field_get` (`codegen/llvm/functions/objects.rs`) with the same
   temporary-print technique the prior session used, on a fixture that
   mirrors `CompilerConfig`'s actual shape: several scalar fields, then a
   `Dict<text,text>` field, then more scalar fields after it (matching
   `profile, log_level, type_inference, values: Dict<>, use_rust_types, ...,
   mcdc_owner_bytes, mcdc_global_bytes, ...`) — print the offset and the
   pointer/bit-pattern actually stored and actually loaded for each field
   name, and check for a duplicate or skipped offset.
3. Separately, check whether `self.field` reads inside an `impl` method body
   (as opposed to external `receiver.field` reads, which is what
   `lower_field_access_expr` traced above covers) go through a different MIR
   lowering function with its own, possibly-divergent offset formula.

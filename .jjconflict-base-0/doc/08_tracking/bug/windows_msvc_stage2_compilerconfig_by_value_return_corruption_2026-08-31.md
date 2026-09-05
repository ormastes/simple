# Windows MSVC Stage 2: CompilerConfig/CompileOptions by-value struct transport corrupts fields non-deterministically

**Date:** 2026-08-31
**Status:** CONFIRMED (measured) as a Windows symptom; root cause identified and FIXED upstream in commit `35b22b6aedf1` (2026-08-31 18:34, landed on macOS lane) — Windows re-verification against a post-fix stage1 still outstanding, see "Session update 2026-08-31 (later)" below. Do not close without that re-run.
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

## 2026-08-31 follow-up #2: offset-formula divergence KILLED; new AggregateCopy/vtable-header asymmetry found (source-reading only, NOT run)

Goal for this session: verify or kill the write-side/read-side field-offset
divergence lead named as the most promising untraced item in follow-up #1,
determine field-count/type sensitivity, and re-assess Windows-specific vs
general.

### Task 1 -- write-side vs read-side offset computation: NO DIVERGENCE (confirmed independently)

All three MIR-lowering sites that compute a struct field's byte offset use
the identical formula `(field_index as u32) * 8`, with `field_index` sourced
from the same `HirType::Struct { fields, .. }` declaration-order enumeration
in every case:

- Write (struct literal): `lower_struct_init_expr`,
  `src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:136-151`
  (offsets built by iterating `struct_fields` from the type registry).
- Read (`obj.field`): `lower_field_access_expr` (same file, ~line 328) --
  `byte_offset = (field_index as u32) * 8`.
- Write (`obj.field = val`): `lowering_stmt.rs:539` -- same formula, same
  registry-sourced `field_index` (from `HirExprKind::FieldAccess{receiver,
  field_index}`, already resolved upstream in HIR).
- Read (callable-field method dispatch): `lowering_expr_method.rs:1421` --
  same formula, `field_index` from the same
  `fields.iter().enumerate().find(...)` pattern over `HirType::Struct`.

No fourth site was found. This lead is dead: offset computation is
self-consistent across every call/read/write path traced. Do not re-chase
it.

Also checked: the previously-flagged "named-arg reorder" mechanism
(`lower_struct_init_fields`, `hir/lower/expr/collections.rs:257+`) already
reorders named constructor args to declared field order (a prior, already
landed root fix, per the comment at `hir/lower/expr/calls.rs:112-119`). It is
a no-op for `CompilerConfig.default()` specifically, because
`config.spl:92-105` already writes the named args in exact declaration
order. This mechanism is not implicated here.

### Task 2/5 -- the one non-trivial mechanism on the zero-mutation `from_env()` path: `copy_if_value_type` / `AggregateCopy`

The diagnostic table in the original record shows `compiler_config.{owner,
global}` already wrong immediately after `from_env()` returns, with no env
vars set -- i.e. on the path `var config = CompilerConfig.default(); ...
(no branch taken); return config`. The only mechanism on that path
that touches field words (rather than just passing a tagged pointer through)
is the F1/S5 value-type copy:

- `copy_if_value_type` (`mir/lower/lowering_core.rs:922-951`) is invoked
  wherever a declared-value-type struct crosses an assignment/return that
  needs snapshot semantics (see call sites in `lowering_stmt.rs` around the
  "aggregate return value... aliased heap handle" comment, and in
  `lower_struct_init_expr`'s per-field boxing loop).
- Its size derivation is `byte_size = (fields.len() as u32) * 8` -- the
  same formula and the same field count as `compile_struct_init`'s
  allocation size (`codegen/llvm/functions/objects.rs:120`, `struct_size`
  computed the same way at the MIR layer). Checked and they agree: the
  "copy allocates the wrong number of bytes" theory is REFUTED.
- The actual codegen, `emit_aggregate_block_copy`
  (`codegen/llvm/functions/objects.rs:145-230`), correctly untags the
  source pointer before reading (`src_tagged & ~7`) and copies word-by-word
  via `rt_alloc` + GEP + load/store, with a branch-free null/tag guard. No
  misalignment from tag-bit handling was found; that theory is also
  REFUTED.

### NEW FINDING -- `AggregateCopy` never applies the vtable-header adjustment that `StructInit`/`FieldGet`/`FieldSet` all apply

`compile_struct_init` adds an 8-byte header before field 0 when the struct
is vtable-bearing (`header_size = u64::from(vtable_symbol.is_some()) * 8`,
`codegen/llvm/functions/objects.rs:33-39`, then `*offset as u64 +
header_size` per field at line ~163). Field reads/writes mirror this: LLVM
codegen adds `+8` via `owner_has_vtable == Some(true)`
(`codegen/llvm/functions.rs:1171,1187`), and the interpreter's
`effective_field_offset` does the same (`codegen/instr/mod.rs:328-331,
1010,1022`).

`emit_aggregate_block_copy` has no equivalent. It allocates exactly
`byte_size.div_ceil(8) * 8` bytes (`byte_size` = field count * 8, no header
term) and copies that many words starting at offset 0 of the untagged
source pointer -- with no `owner_has_vtable`/header parameter anywhere in
`MirInst::AggregateCopy` (`mir/inst_enum.rs`), `copy_if_value_type`, or
`emit_aggregate_block_copy`'s signature. For a vtable-bearing declared value
type, offset 0 of the real object is the vtable pointer word, not field
0: a value-semantics copy (`var x = someVtableBearingStructValue`) would
copy the vtable pointer into the new object's field-0 slot, every
subsequent field would land one word short of where its reader expects it
(since the reader still adds `+8` for the vtable header that the copy never
allocated), and the last real field would never be copied at all. This
produces exactly the observed signature class: pointer/address-shaped
garbage in some slots (the shifted-in vtable pointer, or an adjacent
uninitialized/reused heap word), non-repeating across runs (heap addresses
vary with ASLR/allocator state), not zero (rules out the plain
under-allocation-reads-as-zero theory, consistent with `rt_alloc`
`calloc`-zeroing only the new, correctly-sized region -- the mismatch is a
size/offset error, not a zeroing gap).

This is NOT confirmed as the cause for `CompilerConfig` specifically.
`CompilerConfig` is declared as a plain `struct` with no trait `impl`
providing dynamic dispatch found this session, so it is plausibly not
vtable-bearing, in which case `header_size`/`owner_has_vtable` would be
`false`/`None` throughout and this asymmetry would not fire for it. Whether
`CompilerConfig` ends up in `vtable_type_owners`
(`pipeline/native_project/compiler.rs:1704,1749`) for the actual Windows
Stage 2 build was not checked -- that is the next concrete, cheap step
(grep/instrument `qualify_native_struct_layouts` for the set of struct names
it marks `owner_has_vtable = Some(true)`, or add one temporary print there
in a rebuild). Recorded here as a genuine, separate, real defect regardless
of whether it explains this specific symptom -- it is a live correctness bug
in `AggregateCopy` for any vtable-bearing declared value type, on every LLVM
target, not just MSVC.

### Task 2 -- cheap cross-check attempt: blocked, not a real result

Tried a cheap localization probe (run `CompilerConfig.from_env()` through
the Rust seed's interpreter, via `src/compiler_rust/target/bootstrap/simple.exe
run ...`, to separate "native-only" from "also interpreted"). Blocked
immediately: `CompilerConfig` lives in the compiler's own internal layer
(`src/compiler/00.common/config.spl`), not under a path a plain user `.spl`
script can reach via `use std.common.config` -- the seed reports `Module
"std.common" does not export 'config'`. Did not pursue further (would need
either a fixture inside the compiler's own module tree or the full driver in
the loop, both more expensive than the budget for this check). No
native-vs-interpreted data point was obtained.

### Task 4 -- Windows-specific vs general: unchanged verdict, reconfirmed

Every mechanism read this session -- the three offset-formula sites,
`copy_if_value_type`, `struct_deep_fields`, `emit_aggregate_block_copy`,
`compile_struct_init`, and the vtable-header logic in
`codegen/llvm/functions.rs` / `codegen/instr/mod.rs` -- is shared across all
LLVM targets with no `#[cfg(target_os = "windows")]` or triple-string
branch. Verdict unchanged from the original record and follow-up #1: most
likely GENERAL, not MSVC-ABI-specific, but this is inferred from source
reading only -- not measured on Linux/macOS, which this session (like the
prior one) had no means to run.

### Task 5 -- no fix attempted (per task guidance)

Two real candidate mechanisms are now on the table for a future session with
a working build+run loop, in priority order:

1. Confirm/deny `CompilerConfig` is vtable-bearing for the Windows Stage 2
   build. If yes, the `AggregateCopy` header-omission bug above is a strong,
   well-localized candidate and the fix is narrow: thread
   `owner_has_vtable`/`header_size` through `MirInst::AggregateCopy` and
   `emit_aggregate_block_copy`, mirroring `compile_struct_init`'s existing
   `header_size` term exactly. If no, this mechanism is ruled out for this
   symptom (though it remains a real bug to fix for whatever vtable-bearing
   value types do exist).
2. If not vtable-bearing, the next untraced candidate is `struct_deep_fields`
   / the nested-field deep-copy descriptor (`lowering_core.rs:963-996`) --
   not examined in detail this session for whether `Dict<text,text>`
   (`CompilerConfig.values`) or the nested `TypeInferenceConfig` field could
   desync the flat word-copy loop's `word_index` against the outer struct's
   own offsets.

Per task instructions, this is deliberately left as diagnosis, not a patch:
`AggregateCopy` is core codegen shared by every target and every declared
value-type struct in the compiler, and landing a change to it without first
confirming (1) above risks a silent, wide-blast-radius behavior change on a
hypothesis that may not even apply to the reported symptom.

### Unix-safety note

No source was changed this session (read-only investigation; the one
interpreter-run attempt used a throwaway fixture outside the repo, and
failed before compiling anything of the repo's own code). Zero behavior
change on any target.

## Follow-up #2 (2026-08-31, same day) — precondition (1) checked: FALSE. Lead dead for THIS symptom, but a real adjacent bug found and fixed.

Picked up exactly where Follow-up #1 left off: "Confirm `CompilerConfig` is
actually vtable-bearing in the native lane... Measure or trace it; do not
infer from 'it has methods'."

**`CompilerConfig` is NOT vtable-bearing. Measured, not inferred.**

`vtable_type_owners` (consumed by `qualify_native_struct_layouts`,
`pipeline/native_project/compiler.rs:1749`) is populated in exactly one place,
`pipeline/native_project/imports.rs:930-935`, gated on
`pending_vtable_impls`, which is itself populated at `imports.rs:591-596`
**only** when an `HirImpl` carries `Some(trait_name)` — i.e. an explicit
`impl SomeTrait for Type` block. The MIR-lowering-side twin
(`mir/lower/lowering_core.rs:1870`, `if let Some(ref trait_name) =
hir_impl.trait_name`) gates identically. An inherent `impl Type:` block (no
`for Trait`) never sets `trait_name`, so it can never reach either vtable
set — "has methods" was never sufficient, and the codebase agrees with itself
on this in two independent places.

```
$ grep -n "impl.*for CompilerConfig\|impl CompilerConfig" src/compiler/00.common/config.spl
88:impl CompilerConfig:                     # inherent — no `for X`
$ grep -rn "for CompilerConfig" src/ --include=*.spl
(zero matches, whole tree)
```

`CompilerConfig` (`struct CompilerConfig:`, `config.spl:67`) has exactly one
`impl` block and it is inherent. It implements no trait anywhere in the tree.
Its one nested struct field, `type_inference: TypeInferenceConfig`
(`config.spl:362,375`), is the same: `struct TypeInferenceConfig:` with one
inherent `impl TypeInferenceConfig:` block, zero `for TypeInferenceConfig`
hits. So `owner_has_vtable` resolves to `Some(false)` for `CompilerConfig`
at BOTH the outer-copy level and the one nested-struct-field level that
exists — the vtable-header-omission mechanism this and the prior session
converged on cannot fire for this specific struct's own copy.

**Verdict on task items 1-2: item 1 is FALSE, measured by exhaustive grep
against the actual gating condition (not inferred from method count).**
Per the task's own instruction ("If the lead dies, that is a fine outcome —
say so with evidence"): this lead is DEAD for explaining the reported
`CompilerConfig`/`mcdc_global_bytes` corruption specifically. Item 2 (is the
`AggregateCopy` path reached for `CompilerConfig.default()`/`.from_env()`) is
moot given item 1 is false — the copy path is very likely reached (`struct`
by-value binding is exactly `copy_if_value_type`'s target), but the SPECIFIC
defect this lead named cannot be the cause because there is no header to omit.

**The mechanism itself is real and was independently confirmed as a live,
UNFIXED defect — landed anyway, scoped honestly.** While tracing this,
`codegen/llvm/functions.rs:1002-1013` (pre-fix) carried a standing
`TODO(sj-segv-2026-08-27)` stating verbatim: "this arm has the same
truncation defect the Cranelift arm just had... Unfixed and unverified on
this lane." Cranelift's sibling
(`codegen/instr/closures_structs.rs::emit_aggregate_block_copy`) already
carries the fix, keyed off `ctx.vtable_data_ids.contains_key(type_name)` — a
Cranelift-local mechanism. The LLVM backend had no equivalent lookup and the
TODO explicitly says so. `MirInst::AggregateCopy` and `AggregateFieldCopy`
also already documented the exact gap in their own doc comments
(`mir/inst_enum.rs`) referencing this same bug id, but no field carried the
resolved answer.

**Fix landed this session** (Task 3/4/5 from the newest task brief, executed
despite item-1 being false, because the mechanism is real and independent of
whether it explains THIS symptom):
- Added `owner_has_vtable: Option<bool>` to `MirInst::AggregateCopy` and to
  `AggregateFieldCopy` (`mir/inst_enum.rs`), set to `None` at construction
  (`mir/lower/lowering_core.rs`, both the top-level and
  `struct_deep_fields` sites) — mirrors exactly how `FieldGet`/`FieldSet`
  already carry `owner_has_vtable`, resolved later once the whole-project
  vtable owner set is known.
- `qualify_native_struct_layouts` (`pipeline/native_project/compiler.rs`)
  now resolves it for `AggregateCopy`, recursively over the whole
  `deep_fields` tree (`resolve_owner_has_vtable` /
  `resolve_deep_field_vtables`, new helpers), reusing the identical
  three-way owner-resolution the existing `FieldGet`/`FieldSet` arm uses
  (exact-owner / ambiguous-name tie-break / fail-closed-false).
- `codegen/llvm/functions/objects.rs::emit_aggregate_block_copy` now applies
  the header shift the Cranelift sibling already applies: `byte_size += 8`
  and every `word_index` (including nested, keyed on that field's OWN
  `owner_has_vtable`) shifts by one word when the block being copied carries
  a header. `compile_aggregate_copy`/`emit_aggregate_block_copy` gained the
  new parameter; call sites in `codegen/llvm/functions.rs`,
  `codegen/llvm/emitter.rs` (the `CodegenEmitter` trait's LLVM impl),
  `codegen/emitter_trait.rs`, `codegen/dispatch.rs`, `codegen/mir_interpreter.rs`
  (ignored — the interpreter has no heap layout) and
  `codegen/cranelift_emitter.rs` (ignored — Cranelift keeps its own
  `type_name`-keyed lookup unchanged, to avoid an unreviewed behavior change
  on a lane this session did not verify) were all updated to thread or
  intentionally ignore the new parameter.
- Other callers of `emit_aggregate_block_copy`/`compile_aggregate_copy`
  audited: only the recursive self-call (now passes
  `field.owner_has_vtable` instead of nothing) and the one dispatch call
  site in `compile_emitter_simd_instruction` (SIMD fallback, not the
  primary `AggregateCopy` path — that's handled directly in
  `functions.rs`'s main match arm before dispatch is ever reached for this
  instruction).
- **Blast-radius correction made after first landing this fix (advisor
  review caught it before commit):** `resolve_owner_has_vtable`'s ambiguous-
  name-with-incompatible-layouts branch initially mirrored
  `FieldGet`/`FieldSet`'s hard `Err` exactly, which meant `AggregateCopy`
  could newly turn a previously-successful whole-project compile into a hard
  error purely over a byte-copy header-shift decision — a new failure mode
  `AggregateCopy` never had before this fix, on a code path
  (`resolve_owner_has_vtable`/`resolve_deep_field_vtables`) that had not
  actually executed against any real vtable-bearing struct in this session
  (the regression test constructs `owner_has_vtable: Some(true)` by hand and
  never calls the resolver). Changed the ambiguous branch to resolve `false`
  (no header assumed) instead of erroring — `resolve_owner_has_vtable` is now
  infallible (`bool`, not `Result<bool, String>`); a genuine header/offset
  mismatch for an ambiguous name is still caught by the pre-existing
  `FieldGet`/`FieldSet` arm, which any struct with an accessed field also
  traverses. This keeps the "can only improve, never break" property the
  rest of the change already had.
- **Negative control run** (advisor-requested, in-file rather than via
  `git stash` — stashing `objects.rs` alone breaks its call signature
  against `functions.rs` and fails to compile rather than failing the
  assertion): temporarily hardcoded `let has_vtable = false;` in
  `emit_aggregate_block_copy`, reran the one regression test — it FAILED,
  with the printed IR showing `%aggcopy_alloc = tail call i64
  @rt_alloc(i64 16)` (the pre-fix under-allocation) instead of the required
  `i64 24`. Restored the real line
  (`let has_vtable = owner_has_vtable == Some(true);`), reran — PASSED. The
  test discriminates the fix, not just exercises the code path.

**Verified:**
- `cargo check -p simple-compiler --features llvm` — clean (only 3
  pre-existing unrelated warnings).
- `cargo check --bin simple --features llvm` — clean, same warnings.
- `cargo check -p simple-compiler` (no `llvm` feature, Cranelift-only) —
  clean, confirming the Cranelift lane's untouched behavior still compiles.
- New regression test
  `codegen::llvm::functions::tests::aggregate_copy_of_vtable_bearing_struct_shifts_for_header`
  (`codegen/llvm/functions.rs`): builds a 2-field vtable-bearing `Owner`
  struct (`byte_size: 16`, `owner_has_vtable: Some(true)`), emits
  `AggregateCopy`, and asserts the emitted `rt_alloc` call for the copy
  allocates `i64 24` (`words = (16+8)/8 = 3`), not `i64 16` — the pre-fix
  under-allocation that would drop the last field and shift every other
  field into its neighbour's slot. `cargo test -p simple-compiler --features
  llvm --lib codegen::llvm::functions::tests::aggregate_copy_of_vtable_bearing_struct_shifts_for_header`
  → `1 passed`. (Running it required TWO throwaway, uncommitted
  `#[cfg(unix)]` gates on unrelated pre-existing defects, both reverted
  before committing and neither touched by this session's actual fix:
  `interpreter_extern::memory::ptr_read_u8_tests::maps_protects_and_unmaps_host_memory`
  (test-only, `libc::PROT_READ` etc. used outside any `cfg(unix)` gate) and
  `perf_counters::dump_on_signal` (NOT test-only —
  `extern "C" fn dump_on_signal(sig: libc::c_int)`, `perf_counters.rs:152`,
  uses `libc` unconditionally even though `libc` is a
  `[target.'cfg(unix)'.dependencies]`-only crate per
  `compiler/Cargo.toml:131-132`, and even though the ONE call site that
  references this function, three lines above at `init()`, is already
  correctly `#[cfg(unix)]`-gated with a comment explaining exactly why
  — "`libc` is a cfg(unix)-only dependency of this crate, so the call
  above cannot compile on Windows" — yet the function signature/body one
  page down was missed. This one is graver than the test-only one: it
  broke `cargo check -p simple-compiler --features llvm` outright once
  this session's edits invalidated cargo's incremental cache for that
  file — an earlier `cargo check` in this same session had reported clean
  only because a stale cached artifact for `perf_counters.rs` was being
  reused; `git stash`-ing this session's own changes back out reproduced
  the SAME `E0433` on the unmodified base tree, confirming it is
  pre-existing and target-independent of this session's fix, not caused
  by it. Neither gate was filed as a separate bug record this session —
  flagging both here so the next session doesn't have to rediscover them,
  and so a future `cargo check` failure in either file is not mistaken for
  a regression from this change.)
- Did NOT run the full bootstrap (`run_s2final.sh`) — another bootstrap
  build was already running concurrently in this tree
  (`Get-CimInstance Win32_Process` matched 4 `bootstrap-from-scratch`
  processes at the time), and the task's own guidance says not to start a
  competing one. The fix therefore has LLVM-IR-level and unit-test proof,
  not an end-to-end Stage 2 admission proof.

**Windows-specific vs general, for the mechanism that WAS fixed:** general,
not Windows-specific — nothing in `emit_aggregate_block_copy`,
`compile_struct_init`, or `qualify_native_struct_layouts` branches on target
OS or triple. Any vtable-bearing `struct` copied by value
(`var x = y_of_trait_implementing_struct_type`) under the LLVM backend on
ANY target was hitting this same under-allocation before today; Cranelift
was already immune via its own independent mechanism. This confirms and
closes the open half of `sj_segv_struct_param_field_extract_2026-08-27.md`
for the LLVM lane specifically (that record's own text already named the
Cranelift fix and flagged the LLVM side as the unfixed twin).

**What remains open for THIS bug's actual symptom:** the
`CompilerConfig`/`mcdc_global_bytes` corruption is still unexplained. Per
Follow-up #1's own priority list, item 2 is next and still untraced this
session: `struct_deep_fields` / the nested-field deep-copy descriptor
(`lowering_core.rs:963-996`) for whether `Dict<text,text>`
(`CompilerConfig.values`) or the nested `TypeInferenceConfig` field somehow
desyncs the flat word-copy loop's `word_index` against the outer struct's
own field offsets — a mechanism unrelated to vtables, since neither
`CompilerConfig` nor `TypeInferenceConfig` has one. A fresh session with a
working build+run loop (this one deliberately avoided racing the concurrent
bootstrap) should pick that up directly, or instrument
`copy_if_value_type`/`emit_aggregate_block_copy` with the
`SIMPLE_PERF_COUNTERS`-style level-gated tracing this repo already favors
(see `.claude/rules/commands.md`) to observe the real `byte_size`/`words`
values `CompilerConfig`'s own copy computes at runtime.

## 2026-08-31 follow-up #3: the "flattening" hypothesis KILLED (arithmetic + non-execution); copy/transport family closed; strong NEW lead found — field-name-ambiguity mis-resolved index, not a copy defect at all

Task for this session: check whether `struct_deep_fields` flattens a nested
struct's own fields into the parent's word count, causing the declared field
count and the byte-offset formula to disagree for `CompilerConfig` (which has
a `Dict<text,text>` field and a nested `TypeInferenceConfig` struct field).

### Numbers requested by the task, measured by direct source reading (no rebuild needed — these are compile-time-constant formulas, not runtime values)

- `CompilerConfig` (`src/compiler/00.common/config.spl:67-85`) has **14**
  declared fields, in order: `profile(0) log_level(1) type_inference(2)
  values(3) use_rust_types(4) use_rust_interp(5) use_rust_lexer(6)
  deterministic(7) coverage_enabled(8) mcdc_mode(9) mcdc_owner_bytes(10)
  mcdc_global_bytes(11) mcdc_include(12) mcdc_exclude(13)`.
- (a) declared field count = **14**.
- (c) byte size used by the copy (`copy_if_value_type`,
  `mir/lower/lowering_core.rs:935`) = `fields.len() as u32 * 8` = **112**,
  computed directly from the SAME 14-entry enumeration as (a) — not from (b).
- (d) offsets: `mcdc_owner_bytes` = field index 10 → byte offset **80**;
  `mcdc_global_bytes` = field index 11 → byte offset **88**. Same formula
  `field_index * 8` at all three other sites (struct-literal init, field
  read, field write) — already independently confirmed self-consistent in
  Follow-up #2's Task 1.
- (b) what `struct_deep_fields` returns (`lowering_core.rs:972-1011`) is
  **not a count that should equal (a)** — it is a *sparse, filtered*
  `Vec<AggregateFieldCopy>` containing, for `CompilerConfig`, exactly **one**
  entry: `{ word_index: 2, byte_size: 40 (TypeInferenceConfig's own 5 fields
  × 8), nested: [] }`. `values: Dict<text,text>` at index 3 is correctly
  excluded (`registry.get(fty)` does not match `HirType::Struct` for a
  `Dict`, so it stays shallow — one word, consistent with COW value
  semantics for `Dict` elsewhere in this codebase).

### Flattening mismatch: DOES NOT EXIST — arithmetic kill

`struct_deep_fields`'s `word_index` is the OUTER struct's own
`fields.iter().enumerate()` index (`i` in the loop at
`lowering_core.rs:982`), never a running/flattened counter across a nested
struct's own field count. The returned `Vec<AggregateFieldCopy>` is consumed
by `emit_aggregate_block_copy` (`codegen/llvm/functions/objects.rs:246-306`)
as an ADDITIONAL, purely side-effecting rewrite of specific words *after* the
flat `byte_size`-driven word copy loop already ran — it never feeds back into
`byte_size` or into any other field's offset. So (a)=14 and
(c)=112=14×8 **agree by construction**, and no field after index 2 is
shifted by the nested descriptor. This is a real, complete arithmetic
refutation, not an inference: (a) and (c) are the same formula evaluated
twice, not two independent computations that could drift.

### Correlation cross-check (task item 3): skipped, with reason

The size/offset math is composition-independent — it would produce the
identical `byte_size`/offsets for a hypothetical struct with no nested struct
and no `Dict` field, since neither is consulted. Running the check would
therefore mechanically prove "no difference" without adding information; not
worth the build-slot cost given the four concurrent bootstraps in this tree.

### A second, stronger kill: `AggregateCopy` is never even reached on this path

Independent of the arithmetic: `HirStmt::Return`
(`mir/lower/lowering_stmt.rs:1014-1031`) never calls `copy_if_value_type` —
it only boxes/unboxes for the tagged-value slot and hands back whatever
register `lower_expr` produced, so `return config` returns the SAME aliased
heap handle `config` already held. And the caller's
`var compiler_config = CompilerConfig.from_env()` has a **call** expression
as its RHS, so `Self::hir_expr_is_place(&val.kind)` is `false`
(`lowering_stmt.rs:382`) and the local-binding copy site is skipped too. **No
`AggregateCopy` executes anywhere on the `from_env()` → `compiler_config`
path.** This retroactively explains why leads 1-4 (offset-formula
divergence, vtable-header omission, Dict/nested-struct flattening) all
turned out to be dead ends: every one of them was a hypothesis about the
COPY mechanism, and the copy mechanism is not in the loop for this specific
symptom at all. This closes the whole copy/transport family, not just this
session's assigned member of it.

(Sub-investigation, also closed clean: since `emit_function_drops`
[`lowering_stmt.rs:2209-2257`] emits a `Drop` on every local, including
`config`, in the SAME block right before the `Return` terminator is set, a
use-after-free-via-premature-drop theory was checked and killed —
`MirInst::Drop` is an explicit no-op in the LLVM backend:
`codegen/llvm/functions.rs:1363` — `"Drop and scope tracking not yet
implemented"`. Windows MSVC Stage 2 is the LLVM backend, so this cannot fire
here. Real, but a dead end for this symptom.)

### Re-confirmation run (5th independent measurement, same rejected artifact)

```
DIAG after from_env: owner=770048 global=4325440
DIAG options: owner=1136643962305 global=1 mode_text=
DIAG after cli-apply: owner=1136643962305 global=4325440
error: in-process SMF compile: MC/DC global byte budget must be at least the owner byte budget
```

Correction to the prior session's characterization: `770048` (`0xBC040`) and
`4325440` (`0x420040`) are **not** 47-bit-VA-shaped like the earlier
`140714796318720` reading — they're ~10^5-10^6 magnitude and share the same
low 12 bits (`0x040`), which looks like allocator-rounded size/offset words,
not heap pointers. Don't file this run as "matches the established VA-shaped
pattern" — the garbage is not one consistent distribution across runs, which
itself is a data point (see below). (Also: read `$?` for the compile
invocation directly, not through the `head` pipe used to capture this
excerpt — the prior "rc=0" claims in this doc file's history were `head`'s
status, not the binary's, exactly the pipe-status trap
`.claude/rules/commands.md` warns about generally.)

### THE NEW LEAD: field-name ambiguity mis-resolving to a WRONG STRUCT's field index — not a copy/transport bug at all

Since no copy occurs, only three things remain: the store wrote a wrong
value, the load reads through a wrong pointer/base, or the load uses a wrong
**offset**. The data discriminates: `options.mcdc_global_bytes` reads as `1`
in every one of 5 independent runs — stable, small, sane-looking — sitting
right next to `options.mcdc_owner_bytes`, which is garbage and different
every run. A wrong base pointer or a stray heap overwrite would corrupt
*both* neighbors together (or neither); one stable-looking slot beside one
garbage slot next to it is the signature of each field independently reading
the **wrong offset**, not of a wrong pointer or overwritten memory.

**`mcdc_owner_bytes`/`mcdc_global_bytes` are genuinely ambiguous field
names across two real, unrelated structs in this tree**, with DIFFERENT
indices:

| struct | file | field count | `mcdc_owner_bytes` index | `mcdc_global_bytes` index |
|---|---|---|---|---|
| `CompilerConfig` | `00.common/config.spl:67-85` | 14 | 10 (offset 80) | 11 (offset 88) |
| `CompileOptions` | `00.common/driver_compile_options.spl:3-46` | 35 | 22 (offset 176) | 23 (offset 184) |

By the codebase's own definition of "ambiguous" (`native_project/compiler.rs`
~line 690: *"a field name is ambiguous only when two structs disagree on its
index within the struct"*), this pair qualifies exactly.

**This exact failure mode is independently documented, already found once,
and partially fixed, in this very file** —
`hir/lower/expr/access.rs:709-717`, a standing comment on the "last resort"
receiver-struct-name-inference fallback:

> "...a PARAMETER still carries its AUTHORED type name... Using it here is
> what keeps a declared-type receiver off the receiver-blind 'most fields
> wins' fallback: `CompileContext.create(options: CompileOptions)` was
> resolving `options.mcdc_owner_bytes` through that fallback to MirLowering's
> index 26 (0xd0, past the end of the object) instead of CompileOptions' 22
> (0xb0)."

This is not circumstantial — it names the exact two fields this bug report
is about, and it names the exact "prefer the struct with the most fields"
un-typed-receiver fallback (`type_resolver.rs:629-681`,
`get_field_info`, triggered when `recv_hir.ty == TypeId::ANY`: it scans every
known struct for a field with the matching NAME and picks whichever
candidate struct has the MOST total fields — a receiver-blind guess). The
mitigations that exist (`type_name_hint` for parameters,
`ctx.static_call_type_hints` for locals bound from a static call — both in
`try_resolve_receiver_struct_name_from_expr`,
`access.rs:698-726`) are gated behind `is_ambiguous_global_field(field)` at
the call site (`access.rs:232`), which is only consulted when
`recv_hir.ty == TypeId::ANY` in the first place — i.e. the guard rail exists,
but only fires once the receiver type has already been erased to ANY.

**The +4 index-shift arithmetic this comment names lines up exactly with the
CompileOptions field list and reproduces BOTH measured symptoms:**
`CompileOptions` field 26 is `cli_mode_text` (a `text`, i.e. a pointer —
would print as a large, run-varying, address-shaped integer when
misinterpreted as `i64`) and field 27 is `bootstrap_input_count` (an `i64`
that `run_compile_bootstrap` explicitly sets to `1`, matching the
consistently-`1` `options.mcdc_global_bytes` reading in every one of the 5
measured runs — this was flagged as "plausible but not independently proven"
in the very first version of this doc, and is now proven by exact field
identity, not just plausibility). If the same wrong-struct/wrong-index
resolution applies to `compiler_config` (the smaller, 14-field/112-byte
`CompilerConfig`) rather than `options` (the larger, 35-field
`CompileOptions`), reading at word-index 22 or 26 means reading **176 or 208
bytes into a 112-byte allocation — past the end of the object**, exactly the
phrase the standing comment already uses, and exactly consistent with the
wilder, less-patterned garbage (including the near-full-range
`8243126012946380655` reading) seen for `compiler_config.*` versus the more
patterned garbage seen for `options.*`.

**Also newly found while checking this: `CompileOptions` is itself a
duplicated bare name.** `grep -rn "^struct CompileOptions" src/` finds a
SECOND, unrelated 3-field struct (`debug, optimize, verify`, no `mcdc_*`
fields at all) at
`src/compiler_rust/lib/std/src/tooling/compile_commands.spl` — a
completely different "compile options" concept (for a `compile_commands.json`
style tool) that happens to share the bare name. This does not by itself
explain index 26 (it has no `mcdc_owner_bytes` field to collide on), but it
independently confirms that cross-module same-bare-name struct collision is
a live, present hazard for this exact type name, which is exactly the class
of bug `duplicate_struct_defs`/`unique_struct_owners`/`struct_module_owners`
(`native_project/compiler.rs:708-711`) exist to guard against.

**Not verified this session (no build slot — 4 concurrent bootstraps
running, matching this and prior sessions' constraint):** whether
`populate_global_struct_defs` (which gates `ambiguous_field_names`,
`native_project/mod.rs:875,931,952`) is actually `true` for the Windows
Stage 2 self-hosting build. The gating condition in the CURRENT tree is
`!self.config.no_mangle` (default `no_mangle: false`, so the guard rail
should be ON by default) — **this contradicts the comment directly above it
at `native_project/compiler.rs:686`, which still says "Gated on
`--entry-closure`."** That comment is stale relative to the code it
describes (worth its own tiny doc-only fix, not attempted here since it is
unrelated to this bug). Given the guard rail's default is ON and the
Windows bootstrap script does not pass `--no-mangle`
(`grep -rn "no-mangle" scripts/bootstrap/bootstrap-windows.sh` = no hits),
the mitigation should be active — yet the corruption still reproduces on the
real Stage 2 artifact (5 independent measurements now). This is the
concrete, falsifiable gap for the next session: **either the mitigation
IS active and still insufficient for this specific case (`compiler_config`,
a local bound from a cross-module static call, vs. `options`, a directly
annotated parameter — the two code paths in
`try_resolve_receiver_struct_name_from_expr` are different and the local
path was not proven to work, only shown to exist), or it is not actually
active for this build for a reason not found this session (e.g. a build flag
this session didn't check, or the self-hosting compile-of-the-compiler path
not routing through `native_project` the same way user code does).**

### Recommended next step (concrete, cheap, no full bootstrap required)

The compiled-in tracing already exists and is exactly what this needs
(`hir/lower/expr/access.rs:316-348`, `type_resolver.rs:647-679`): set
`SIMPLE_FIELD_INDEX_COUNT_ONLY=1` (or enable `trace_field_get_enabled()`,
check `hir/lower/mod.rs:221` for its own env var) while COMPILING
`driver_types.spl`/`config.spl` — i.e. during a Stage 1→Stage 2 build step,
not while running the already-built Stage 2 binary against a hello-world
(the trace fires at HIR-lowering time, which already happened once to
produce the `.rejected` artifact; running that artifact again cannot
reproduce the trace). This needs either the sanctioned bootstrap script with
the env var exported, or reconstructing its Stage-1-compiles-Stage-2 command
line to compile just the driver module tree standalone — the latter was
attempted and blocked by three unrelated toolchain defects in Follow-up #1
(runtime-bundle single-directory assumption, `lld-link` GNU-argv mismatch,
missing `-lc`/`__main` for a raw `ld` MinGW link) — those blockers apply to
producing a RUNNABLE binary, but do NOT block a `--format=smf`-only compile
that never needs to link, which is a promising unexplored shortcut for next
time. Grep the resulting stderr for `[FIELD-TRACE]`/`[FT2]` lines naming
`mcdc_owner_bytes`/`mcdc_global_bytes` and read off the actual chosen struct
name and index directly — this settles the lead with a real number instead
of an inferred one.

### Windows-specific vs. general — verdict for THIS lead

**Inferred, not proved, same as every prior session.** Every mechanism in
this lead (`get_field_info`'s ANY-typed fallback, `is_ambiguous_global_field`,
`try_resolve_receiver_struct_name_from_expr`, `populate_global_struct_defs`)
is in the shared HIR-lowering front end, upstream of and shared by every
codegen backend and every target — nothing branches on `target_os` or
triple anywhere in the files read this session. If this lead is confirmed,
it is very likely a GENERAL defect (any target, any backend, whenever a
field name collides across two structs with different indices), not an
MSVC-ABI-specific one — but, as with every prior session, this repo offers
no way to run a second-platform measurement from here, so this stays a
source-reading inference, not a proof. Do not upgrade it without a real
non-Windows measurement.

**Explicitly not chased, flagged so nobody spends a day on it:** a Win64
register-allocation/calling-convention theory (distinct from the
already-refuted aggregate-classification theory) was briefly considered
mid-session as an alternative explanation for the field reads, but dropped
for lack of any evidence — nothing in this session's reading pointed at the
register allocator, and the field-ambiguity lead above already explains both
measured symptoms without it. Unevidenced; do not treat as a lead.

### What was NOT done

No source files were changed (read-only investigation this session; the one
executable invocation was re-running the ALREADY-BUILT, ALREADY-diagnosed
`.rejected` artifact for a 5th confirmation, not a new build). No fix
attempted, per task guidance and because the exact mechanism (which struct
the fallback picks, and why the existing `type_name_hint`/
`static_call_type_hints` mitigation doesn't prevent it here) is still not
directly observed, only inferred from static analysis converging with an
existing code comment describing the same symptom for a sibling field
access. Zero behavior change on any target.

## Session update 2026-08-31 (later): the lead is CONFIRMED and a fix has LANDED - Windows re-verification still outstanding

This session picked up exactly where the prior one stopped and answered its
open question. Repo: `simple-rebase`, branch
`work/windows-bootstrap-msvc-rebased`.

### 1. Field identities at indices 26/27 - VERIFIED, exact match

Re-counted `CompileOptions` fields (0-based, `src/compiler/00.common/driver_compile_options.spl:3-45`,
comments and blank lines excluded from the count):

```
22  mcdc_owner_bytes: i64 = 0
23  mcdc_global_bytes: i64 = 0
24  allowed_families: [text]
25  build_mode: text
26  cli_mode_text: text            <- predicted, CONFIRMED
27  bootstrap_input_count: i64     <- predicted, CONFIRMED
28  bootstrap_input_0: text
29  bootstrap_input_1: text
```

`bootstrap_api.spl:10` unconditionally sets `options.bootstrap_input_count = 1`
before every bootstrap compile. The +4 index-shift arithmetic in the prior
session's lead is exactly right.

### 2. The mitigation is not just "exists" - it is the VERIFIED, LANDED root-cause fix, and it predates/upstreams this doc's remaining gap

While this session was investigating, commit `35b22b6aedf1`
("fix(macos): unbreak the macOS bootstrap lane - 10 platform defects + 5
compiler defects (#97)", 2026-08-31 18:34:03 +0900) landed on this branch.
It independently root-caused the identical bug - same symptom
(`mcdc_owner_bytes`/`mcdc_global_bytes` corruption in
`CompileContext.create`), same mechanism (`get_field_info`'s ANY-typed
"most fields wins" fallback), same numbers (`CompilerConfig` field 10/0x50,
`CompileOptions` field 22/0xb0, `MirLowering` field 26/0xd0 winning by field
count) - on the macOS lane, and fixed it with four changes:

1. `type_resolver.rs`: the ANY-branch and wildcard-branch "most fields wins"
   loops now refuse to guess (`best = None`) when `is_ambiguous_global_field`
   is true, instead of picking the struct with the most fields.
2. `module_pass.rs` (both pre-registration passes): now also walk
   `Node::ExportUseStmt`, not just `Node::UseStmt` - `driver_types.spl:7` is
   `export use compiler.common.driver_core_types.*`, and `CompileOptions`
   was never registered as a named type through that route, which is why its
   receiver erased to `ANY` in the first place.
3. `native_project/imports.rs`: the whole-program return-type map now also
   collects methods declared inside `impl` blocks (was `Node::Function`
   only), so `CompilerConfig.from_env()`'s return type is discoverable.
4. `hir/lower/module_lowering/function.rs` / `expr/access.rs`: the
   `LocalVar::type_name_hint` mechanism read about last session is confirmed
   populated unconditionally for every parameter with an explicit type
   annotation (`module_lowering/function.rs:658-664`), and is additionally
   extended with `FunctionContext::static_call_type_hints` for a local
   initialized from a static call whose declared return type is known
   (covers `compiler_config`, made discoverable by fix 3).

Answer to the prior session's decisive open question ("is
`populate_global_struct_defs` active for this build?"): yes, confirmed -
`native_project/mod.rs:875` gates the whole `imports` value (including
`populate_global_struct_defs: true` at `mod.rs:931`) on
`!self.config.no_mangle`; `no_mangle` defaults `false` (`mod.rs:460`) and is
set `true` only by an explicit `--no-mangle` CLI flag
(`driver/src/cli/native_build.rs:97,239`), which the Windows bootstrap script
never passes. But the real answer, per 35b22b6's own investigation, is that
this single mitigation was necessary but NOT sufficient on its own - it took
the `ExportUseStmt` registration fix plus the impl-method return-type
collection fix plus the static-call hint extension, in combination, to close
both the `options` and `compiler_config` receivers.

### 3. Which access mis-resolves - BOTH, confirmed by the fixing commit's own disassembly

The commit body includes real ARM64 disassembly from a genuinely built and
run macOS Stage 2 binary, at successive points in its own investigation:

```
ldr x8, [x28, #0xb0]   ; options.mcdc_owner_bytes    CompileOptions f22  fixed  (after fix 2)
ldr x9, [x22, #0xd0]   ; compiler_config.owner       MirLowering    f26  still wrong (before fixes 3+4)
```

`options` (a directly annotated function parameter) was fixed first, by the
`ExportUseStmt` registration fix alone. `compiler_config` (a local bound
from `CompilerConfig.from_env()`, a cross-module static call) needed the two
additional fixes because a local's type-resolution path differs from a
parameter's. Both receivers are now covered by the landed commit.

### 4. Cheap-oracle attempt this session - inconclusive, not pursued further

Confirmed no bootstrap process was actually running (the process-list match
in the task brief was a false positive: it matched this session's own
`Get-CimInstance` query string, which itself contains the literal text
`bootstrap-from-scratch`). Found a freshly built seed,
`src/compiler_rust/target/release/simple.exe`, timestamped 18:35:08 - 65
seconds after 35b22b6 landed - so it already contains the fix. Attempted the
prior session's own recommended cheap test: `SIMPLE_TRACE_FIELD_GET=1` plus
`native-build --source src/compiler --source src/app --source src/lib
--entry src/app/cli/bootstrap_main.spl --emit-object` (object-only, no link,
so it should be fast and MSVC-toolchain-independent). Result: inconclusive
within a 10-minute budget - sporadic `error: semantic: invalid operation:
cannot slice value of type str with step` at `driver_types.spl:7:1` on some
shards while other shards proceeded (the repo's own `parse-shard`/
`hir-shard` retry machinery was visibly reclaiming and re-queuing shards),
and `SIMPLE_TRACE_FIELD_GET` turned out to instrument a different
(interpreter-time) path than native codegen - only 29 `[TRACE FieldGet]`
lines fired across the whole build, none for `mcdc_owner_bytes`/
`mcdc_global_bytes`/`CompileContext`, so it is not the right lever for this
codegen path. No exit-code marker was ever written to the captured log, so
the run's actual outcome is unknown and a background-task "completed" status
notification could not be reconciled with the log content and should not be
trusted as a pass. Recorded so the next session does not repeat it. Also
worth noting: this checkout's `git status` currently reports extensive
deletions (`src/compiler/driver`, `src/compiler/blocks`, `src/std`, etc. all
`D`) that did not stop this build from finding those files on disk - worth
an independent look before trusting any build result from this checkout. No
source files were changed and no process was left running (build and
monitor tasks explicitly stopped at the end of this session).

### 5. General vs. Windows-specific - verdict upgraded from "inferred" to "general, with cross-platform empirical confirmation; Windows re-run still pending"

Prior session: "inferred, not proved... this repo offers no way to run a
second-platform measurement." That gap is now closed in the general
direction: the identical mechanism, on a different real platform
(macOS/aarch64 vs. the Windows/x86_64-msvc this doc covers), with a real
compiled-and-run Stage 2 binary, went from failing at the same MC/DC
buffer-cap guard this doc documents to linking, running, and reporting
`simple-bootstrap 1.0.0-rc.1` after the four fixes above (per 35b22b6's own
commit body - Stage 2 then hit a different, unrelated hang in
`lower_mir_storage_project_fields_v1`, confirming the mcdc-corruption
failure mode specifically was cleared and progress moved past it). Nothing
in the four fixed files branches on `target_os` or triple; the mechanism is
squarely in the shared HIR front end used by every backend and target. This
is real evidence, not just static-source inference, but it is evidence from
the OTHER platform - this doc's own platform (Windows/MSVC) has not yet been
re-run against a stage1 built from 35b22b6 or later. The Windows `.rejected`
artifact analyzed across all sessions on this doc
(`build/w/stage2/x86_64-pc-windows-msvc/simple.exe.rejected`, born
16:32:03, modified 16:43:14) unambiguously PREDATES the fix commit
(18:34:03) and must not be re-cited as evidence of an unfixed Windows
Stage 2 - it was built before the fix existed.

### Recommended next step

Run the sanctioned Windows bootstrap
(`scripts/bootstrap/bootstrap-from-scratch.sh`) from a stage1 built at or
after `35b22b6aedf1`, through Stage 2 admission, and record whether the
MC/DC buffer-cap sanity failure recurs. If it does not, this doc's status
should move to FIXED, cross-referenced against
`stage2_struct_field_offset_model_mismatch_oob_read_2026-08-30.md` (the fix
was authored and verified there against the macOS symptom; this doc's
remaining job is to supply the Windows-side confirmation, not a second
independent fix).

**Status update: still CONFIRMED (measured) as a Windows-observed symptom,
but the underlying mechanism is now believed FIXED upstream, unverified on
Windows.** Do not mark this doc resolved without a fresh Windows Stage 2 run
against a post-35b22b6 stage1.

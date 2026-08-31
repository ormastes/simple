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

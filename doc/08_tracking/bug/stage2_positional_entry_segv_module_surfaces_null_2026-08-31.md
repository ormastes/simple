# Stage-2 self-hosted compiler SEGVs on a positional entry — `module_surfaces` reads as NULL

- **Filed:** 2026-08-31
- **Status:** OPEN — isolated to one instruction, cause not yet found
- **Blocks:** Stage-2 admission, therefore Stage 3, therefore Stage 4/5
- **Platform:** observed on aarch64-apple-darwin. NOT established as macOS-specific — see below.

## Symptom

Stage-2 admission fails its sanity gate:

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.0-rc.1
                        unsupported_status=1 frontend_status=1 candidate_unchanged=true
rejected Stage 2 binary preserved: build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected
```

The bootstrap driver reports this as UNDIAGNOSABLE ("the stage failed with no
error message of any kind"). Re-running `candidate_frontend_smoke` by hand
against the rejected binary produces the real message:

```
candidate_frontend_smoke: candidate CRASHED (signal 11, rc=139) native-building
a two-line hello world with a positional entry
```

## The A/B that isolates it

Same rejected binary, same fixture, same flags, one difference:

| invocation | result |
|---|---|
| `native-build ... --entry <fixture>.spl` | **rc=0** |
| `native-build ... <fixture>.spl` (positional) | **rc=139 (SIGSEGV)** |

Fixture is two lines: `fn main():` / `print("hello")`.

These are NOT the same code path, which is the whole point. `--entry` routes to
`run_rt_native_build` and delegates to the Rust FFI. The positional form is
detected by `native_build_single_spl_positional`
(`src/app/cli/bootstrap_main.spl:243`) and built through the **pure-Simple
CompilerDriver** instead. So `--entry` never exercises the self-hosted path, and
until upstream added this probe (`22ab5ea482a`, "Stage 2/3 admission never
exercised the positional entry form") nothing did.

## Fault, exactly

```
EXC_BAD_ACCESS (code=1, address=0x8)
frame #0  module_surface_registry_index + 28
frame #1  HirLowering.surface_index_for_name
frame #2  HirLowering.resolve_import_symbols
frame #3  HirLowering.lower_module
frame #4  HirLowering.lower_parser_module_unstub
frame #5  CompilerDriver.lower_and_check_impl
frame #6  CompilerDriver.compile
frame #7  compiler_driver_run_compile
frame #8  app.cli.bootstrap_main.run_native_build_bootstrap
```

Faulting instruction:

```
-> ldr x0, [x6, #0x8]        ; x6 == 0
   and x7, x0, #0x7
   cmp x7, #0x1
```

`x6 == 0` and the fault address is `0x8`, so the BASE is null. The two
instructions after it are the heap-box tag test (`(v & 7) == 1`), i.e. this is
the standard field load + tag check sequence.

Source: `module_surface_registry_index.spl:78`, `registry.index_by_name.len()` —
the FIRST field read of the function's first line. So the `registry` argument
itself arrives as raw 0, and nothing inside this function is at fault.

Caller: `module_lowering.spl:503`, `module_surface_registry_index(self.module_surfaces, name)`.

## Why this is surprising

`HirLowering.module_surfaces` is declared **non-optional** (`types.spl:70`,
`module_surfaces: ModuleSurfacesByName`), and every construction path sets it:

- `types.spl:431` — the struct literal passes `module_surfaces: empty_module_surfaces`,
  built from `ModuleSurfacesByName.empty()` at `:380`.
- `hirlowering_for_module` (`:507`) and `hirlowering_for_module_with_diagnostics`
  (`:513`) both assign `lowering.module_surfaces = module_surfaces` after construction.

So a non-optional field, initialised on every path, reads as 0 at runtime in the
self-hosted binary. Construction is not the problem; the value is lost between
construction and use.

## Candidate causes, none confirmed

Sibling classes already recorded in this repo, listed so whoever picks this up
starts from the known population rather than from scratch:

- defaulted struct fields left uninitialised in native builds
- zero-init array elements reading raw 0 instead of the nil sentinel 0x3
- text/aggregate through a struct field arriving as a raw int across the staged
  native ABI (`mir_lowering_types.spl:574-581` documents the aggregate-argument
  corruption directly)
- cross-module field/Option poison

The `x6 == 0` detail argues specifically for a lost/never-stored field rather
than a mis-tagged one: a corrupted-but-present value would be non-zero and would
fault at a wilder address, as the `0xf198715900000000` faults in this lane did.

## NOT established

- **Not established as macOS-specific.** It was observed on
  aarch64-apple-darwin, but nothing here is platform-conditional and the path
  was unexercised everywhere until the upstream probe landed. Anyone with a
  Linux box should run the same A/B before this is filed as a Darwin defect.
- **Not caused by the positional-entry fix in this branch** (`838d0ba5bd8`,
  Rust-side `native_build.rs`). That fix changes the SEED's argument parsing;
  the crashing binary is the self-hosted Stage-2 compiler, whose argument
  handling comes from `bootstrap_main.spl`. The upstream Simple-side shim at
  `bootstrap_main.spl:232-241` independently documents the very same seed defect
  the Rust fix repairs, which is corroboration that the fix is right, not a
  cause of this crash.
- Whether `ModuleSurfacesByName.empty()` itself returns a null-representable
  value under self-hosted codegen has NOT been checked. That is the cheapest
  next probe.

## Reproduce

```sh
C=build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected
D=$(mktemp -d)
SIMPLE_BOOTSTRAP=0 SIMPLE_NO_STUB_FALLBACK=1 "$C" native-build \
  --backend cranelift --runtime-bundle core-c-bootstrap --entry-closure \
  --cache-dir "$D/c" --mode one-binary --output "$D/hw" \
  scripts/check/cert/redeploy_gate/fixtures/hello_world.spl
# rc=139; add --entry before the path for rc=0
```

---

## ROOT CAUSE FOUND (2026-08-31) — bare `.unwrap()` mis-dispatches to `Poll.unwrap`

**Status: DIAGNOSED. The defect is in the RUST SEED's method-name resolution,
not in any `.spl` source.**

### What was measured, not inferred

Binary under test: `build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`,
32010840 bytes, mtime 2026-08-31 04:21,
sha256 `3db6a922e3d856ef62d25e4e5f494a8afd4e4ad32e7a7b2541809b711809cdd0`.

lldb on the live crash (three runs, same result every run):

1. Breakpoint on `hirlowering_for_module_with_diagnostics` is hit from
   `lower_and_check_impl+1632` with **`x1 == 0`**. `x1` is the
   `module_surfaces` argument. So the value is already 0 *before* the
   `HirLowering` is constructed — the field store is faithful.
   Disassembly confirms the store: `str x1, [x7, #0x58]`, and `0x58` is
   field index 11 = `module_surfaces`. Nothing clobbers it later:
   `begin_module` (context_helpers.spl) writes 0x8..0x50 and 0x60.. and
   **skips 0x58**, exactly as its comment claims.

2. The `if self.ctx.module_surfaces != nil:` branch IS taken
   (breakpoint at `lower_and_check_impl+1048` hits). Inside that branch the
   emitted code is:

   ```
   ldr  x0, [x5, #0x80]          ; self.ctx.module_surfaces
   adrp x5, 0x100ae1000 ; add #0x1b4
   blr  x5                        ; -> lib__nogc_async_mut__async__poll__Poll_dot_unwrap
   str  x0, [sp, #0x448]          ; retained_module_surfaces
   ```

   `.unwrap()` on `Option<ModuleSurfacesByName>` was bound to
   **`lib.nogc_async_mut.async.poll.Poll.unwrap`**. That method matches
   `Poll.Ready(value)`; an `Option.Some(x)` payload does not match, the native
   match falls through, and the function returns raw **0**.

### 7-second reproducer (no bootstrap needed)

Built with the Rust seed
(`build/bootstrap/rust-authority-338539e5.../target/release/simple`,
mtime 2026-08-31 03:25) using the same flags the bootstrap script uses for
Stage 2 (`--backend cranelift --runtime-bundle core-c-bootstrap
--entry-closure --mode one-binary`), 57 files, 6.6s:

```simple
use compiler.hir.hir_lowering.module_surface.{ModuleSurfacesByName}
use std.nogc_async_mut.async.poll.{Poll}          # any bare-`unwrap` provider

class Ctx:
    module_surfaces: ModuleSurfacesByName?
    sources: [i64]

fn drive(ctx: Ctx) -> ModuleSurfacesByName:
    if ctx.module_surfaces != nil:
        return ctx.module_surfaces.unwrap()       # returns raw 0
    ModuleSurfacesByName.empty()
```

Result matrix (each variant built and RUN; counts are per-variant verdicts,
not a sequence):

| variant | result |
|---|---|
| `.unwrap()` on an `Option<Class>` **field**, `Poll` imported | **SIGSEGV (rc=139)** |
| same, with the `Poll` import removed | rc=0 |
| same, `use std.nogc_sync_mut.failsafe.core.*` instead of `Poll` | **SIGSEGV (rc=139)** |
| `.unwrap()` via a typed local `val o: T? = ctx.f` | **SIGSEGV** |
| `ctx.f ?? T.empty()` | rc=0 |
| `if val x = ctx.f:` | rc=0 |
| `match ctx.f: case Some(v)/case None` | rc=0 |

So the hijack is **not specific to `Poll`** — `FailSafeResult.unwrap`
(`src/lib/nogc_sync_mut/failsafe/core.spl:140`) does it too, and there are 13
`fn unwrap` definitions under `src/`. Renaming `Poll.unwrap` is therefore NOT
a fix; it just hands the hijack to the next provider. This was tested, not
assumed.

### Where the seed defect is

`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`,
`resolve_method_call_static` (defined :724).

There IS already a guard for bare `unwrap | unwrap_or | unwrap_err | is_some |
is_none | is_ok | is_err` — its comment even names `FailSafeResult.unwrap` as
the hazard — but it sits in the **`else` (resolution-FAILED) branch**, after
`if let Some(resolved) = resolve_name_variants(...)`. When any module in the
closure publishes a bare `unwrap` entry into the use/import map,
`resolve_name_variants` **succeeds**, `*func_name` is rebound, and the guard is
never reached. This is the identical fail-open the string-builtin guard was
hoisted above `resolve_name_variants` to close on 2026-07-25 (see that guard's
comment in the same function).

The obvious seed fix — hoist the enum-helper list to the same early position —
is **known to have been tried and reverted**: the in-file comment records that
hoisting the enum-helper and numeric lists "broke legitimate resolution-success
rebinds (the compiled interpreter's own Option helpers printed `<unknown>` for
every text-option `??`, 2026-07-25)". So the seed fix needs a narrower
predicate (e.g. hoist only when the resolved candidate's owning type is not the
receiver's static type, or only for receivers whose static type is a known
`Option`/`Result`). Not made here: repo rule is not to patch the seed
unilaterally once the defect is proven to be the seed's.

### Answers to the two hypotheses this bug doc previously carried

- **`ModuleSurfacesByName.empty()` is NOT null-represented.** Disproved
  directly: probe binaries built against the REAL types
  (`hirlowering_for_module` / `_with_diagnostics` + `begin_module` +
  `surface_index_for_name`, 274-file closure) print
  `ms_nil=false`, `l_ms_nil=false`, `sfn=-1` and exit 0. An all-empty
  aggregate is a normal non-zero heap value.
- **Not a lost/never-stored field, and not a struct-layout divergence.** The
  field store is emitted at the correct offset and the value handed to it is
  already 0.

### Blast radius

Every `Option.unwrap()` / `Result.unwrap()` call site compiled by the seed in a
closure that contains any bare-`unwrap` provider is at risk. `src/` has 4254
`.unwrap()` call sites. Patching them in pure Simple is not a fix; the seed
resolution is.

## 2026-08-31 — measured after the `??` substitution + rt_heap_ref_wellformed restore

Rebuilt Stage 2 via the sanctioned script
(`--full-bootstrap --stop-after-stage2 --mode=dynload --backend=cranelift
--incremental-unlimited`). New binary:
`build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`, 32007416 bytes,
mtime 2026-08-31 05:29,
sha256 `5d20345bef9dc49f324f3e3c1ea2f636839ba03f14e28f0343c257b1629e30a7`.

**The SEGV documented at the top of this file is GONE.** HIR lowering now runs
to completion on the positional two-line fixture:

```
[build] hir 0/1 step 2/6 ... scripts.check.cert.redeploy_gate.fixtures.hello_world
[bootstrap-error-count] source_idx=0 point=post-lowering  count=0
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0
[bootstrap-error-count] source_idx=0 point=post-store      count=0
[build] hir 1/1 step 2/6 ... complete
```

Previously the process died mid-`hir 0/1` inside
`module_surface_registry_index`. Neither that frame nor
`surface_index_for_name` appears in any backtrace now.

**The gate still fails, at a NEW and unrelated site.** `candidate_frontend_smoke`
returns 1 in BOTH modes (`CANDIDATE_FRONTEND_BOOTSTRAP=0` and `=1`), rc=139,
and the fault has moved:

```
[ERROR] phase 3 FAILED
EXC_BAD_ACCESS (code=1, address=0xc0)
frame #0  CompileContext.has_errors + 4          <- null receiver
frame #1  CompilerDriver.compile + 6432
frame #2  compiler_driver_run_compile
frame #3  app.cli.bootstrap_main.run_native_build_bootstrap
```

Two separate open questions, neither of which is this record's defect:

1. why phase 3 reports FAILED with an empty error list while every
   `bootstrap-error-count` receipt reads 0, and
2. why `self.ctx` is null on the failure path in `CompilerDriver.compile`.

Both should be filed and chased separately. This record's own symptom is
resolved; the record stays open only until the two follow-ups have homes.

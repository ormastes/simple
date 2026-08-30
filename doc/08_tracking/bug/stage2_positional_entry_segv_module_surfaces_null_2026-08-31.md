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

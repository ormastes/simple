# Stage 4 full CLI cannot be linked: 579 codegen-emitted runtime symbols have no definition (2026-09-01)

Status: **OPEN**. This is the terminal blocker for the arm64 WM+Vulkan
pixel-evidence lane, and it is not arm64-specific — it is the host x86_64
full CLI.

## Why this build was attempted

`scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` refuses every
Rust seed by design and requires a pure-Simple compiler that can run
`os build --scenario=…` — i.e. a **Stage 4 full CLI**
(`src/app/cli/main.spl`), not a stage binary
(`src/app/cli/bootstrap_main.spl`, `compile`/`native-build` only). See
`arm64_attested_build_rejects_rust_seed_by_design_2026-09-01.md`.

## Reproduce

Fresh `origin/main` (`5e09b3ef2fd`) + PR #273's three commits, fresh
`cargo build --release --bin simple` seed, full 3-stage bootstrap run (stages
built; see `bootstrap_stage_determinism_mismatch_fresh_seed_2026-09-01.md` for
its own failure). Then, with the produced Stage 3 binary:

```
SIMPLE_CACHE_SCOPE=goal2arm64s4 \
  bootstrap/stage3/x86_64-unknown-linux-gnu/simple native-build \
  --source src/app --entry src/app/cli/main.spl --entry-closure --strip \
  --threads 8 --timeout 1200 -o build/stage4/simple
```

## Result — rc 1, no artifact

```
Link failed. Objects kept at: .../.simple/native-objects-PKkY6n
Build failed: 579 runtime symbol(s) referenced by generated code have no
definition in any linked object, runtime archive, or system library:
rt_alloc_page_aligned, rt_array_min, ... rt_cli_dispatch_rust,
rt_cli_handle_compile, rt_cli_run_lint, rt_cli_run_tests, ...
rt_cranelift_* (~90), rt_cuda_* (~40), rt_vulkan_* (~60), rt_sqlite_* (~30),
rt_rocm_*, rt_simd_*, rt_winit_*, rt_webgpu_*, rt_ws_*, ...
spl_backend_plugin_run_v1, spl_fonts_call_layout_text
```

The compiler's own diagnostic states the consequence exactly:

> The native link tolerates undefined symbols, so this would produce a binary
> with a NULL GOT slot per name and SEGV on the first call -- exactly the
> failure that made every self-hosted stage binary crash on hello world
> (rt_unwrap_or_trap, 2026-08-21).

`SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` is offered as a bypass and was **not** set:
it is forbidden by the lane rules and would manufacture precisely the
crash-on-first-call binary described above.

## Relationship to the existing ADVISORY guard

`scripts/check/check-no-unresolved-runtime-symbols.shs` (added 2026-08-21) is
already honestly RED with **83** codegen-emitted names undefined in the C
runtime archive. This measurement is the same defect class at full-CLI scope:
**579** names. The guard's promotion criterion ("promote once a redeploy makes
it green") therefore cannot be met — the redeploy is what is blocked.

Note the classes involved: `rt_cli_*` (the CLI's own dispatch surface),
`rt_cranelift_*` (the AOT backend the self-hosted compiler needs to compile
anything), and large optional-feature families (`rt_cuda_*`, `rt_vulkan_*`,
`rt_rocm_*`, `rt_sqlite_*`, `rt_winit_*`, `rt_webgpu_*`). The last group looks
like the `RT_OPTIONAL_SYMBOLS` list in
`src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs` not covering
what the full-CLI entry closure now pulls in; the `rt_cli_*` and
`rt_cranelift_*` groups do not, and look like genuinely missing providers.

## Net effect on the arm64 lane

No admissible compiler can be produced, so
`arm64_desktop_engine2d_attested_build_reason=compiler-version-invalid` cannot
be cleared, no `build/os/simpleos_arm64_desktop_engine2d.elf` can be attested,
and the AAVMF -> `BOOTAA64.EFI` -> `kernel.elf` `protocol: linux` handover
remains **UNPROVEN**. No boot was attempted.

# Bug: seed `native-build` of `src/app` segfaults — blocks bootstrap Stage 1

**Date:** 2026-06-29
**Area:** native-build / bootstrap (seed compiler AOT path)
**Severity:** high (blocks `bin/simple build bootstrap`, i.e. self-hosted redeploy)

## Symptom

`bin/simple build bootstrap` fails at **Stage 1** with `Compile failed (exit
None)`. The underlying seed command **segfaults (exit 139, core dumped)**:

```
build/bootstrap/full/x86_64-unknown-linux-gnu/simple native-build \
  --source src/app --entry-closure --strip --threads 1 --timeout 180 \
  --entry src/app/cli/bootstrap_main.spl -o bootstrap/stage1/simple \
  --backend=llvm-lib
# -> Segmentation fault (exit 139), no compile diagnostic
```

## Proven pre-existing (differential)

Reverting an unrelated in-flight change (the `variants/` resolver hook in
`module_resolver/{types,resolution}.spl`) to a **clean tree** and re-running the
exact Stage 1 command **still segfaults (exit 139, core dumped)**. So the crash
is independent of source edits to the resolver — it is in the seed's native-build
AOT path for the full `src/app` compile.

## Impact

- Self-hosted redeploy via bootstrap is blocked, so any pure-Simple compiler
  change (e.g. the `variants/` overlay resolver hook) cannot be deployed into the
  running `bin/simple` and verified at the binary level.
- Distinct from the recently-fixed native-build worker *timeout* and
  *entry-closure scoping* issues, and from `native_build_const_eval_int_letter`
  (a const-eval bug) — this is a hard segfault with no diagnostic.

## Triage (2026-06-29): broken for hello-world, both binaries

native-build only accepts `--backend=llvm-lib` (c/cranelift/auto are rejected:
"native-build requires --backend=llvm-lib in the pure Simple command path"). With
that backend:

- **Stale bootstrap seed** (`build/bootstrap/full/x86_64-unknown-linux-gnu/simple`,
  25.7 MB): **segfaults (exit 139) on a 2-line hello-world** — empty log, crashes
  before any compile output. So the crash is *not* scale- or `src/app`-specific;
  the seed's llvm-lib path is broken at init.
- **`bin/simple`** (self-hosted `bin/release/.../simple`): does NOT segfault but
  fails native-build of the same hello-world with
  `error: semantic: undefined field 'id': cannot access field on value of type
  'nil'` (preceded by `[DEBUG FIELD ACCESS] ... receiver expr: Identifier("id")`).
  A distinct nil-field bug in the AOT pipeline.

Neither binary can native-build a hello-world → the self-hosted bootstrap/deploy
path is unusable for ANY pure-Simple compiler change right now, independent of
the change being deployed.

## Next step

Capture the core / run under a debug seed to localize the segfault in the
native-build pipeline (likely codegen/linker stage given `--backend=llvm-lib`).
Until fixed, binary-level verification of self-hosted compiler changes must use
an alternate path (e.g. Rust-seed cargo build for resolver parity).

## Superseded — see `bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`

This doc's SIGSEGV (Linux x86_64 seed, 2026-06-29) is a distinct earlier
symptom from a different platform/seed than the actively-tracked macOS aarch64
Stage-1 wall. All current diagnosis and fixes (SIGSEGV elimination via
`llvm_build_call2` Name NUL-termination, and — as of 2026-07-10 — elimination
of the two "Function return type does not match operand type of return inst"
IR-verifier errors via named `Ret`-case fixes in `llvm_lib_translate.spl`) are
tracked in `bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`.
As of 2026-07-10 (emission-wall session), Stage 1 is SIGSEGV-free,
IR-verification-clean, and object-file emission now **succeeds** (fixed a
triple-unaware `Host` CPU-string leak in `llvm_target.spl` and an ELF-only
magic check in `linker_wrapper_helpers.spl` that rejected valid Mach-O
objects on this aarch64 Mac host). Stage 1 still fails overall on a new,
unrelated frontend wall (`semantic: method 'replace' not found on value of
type str in nested call context`) — see that doc for the current state.

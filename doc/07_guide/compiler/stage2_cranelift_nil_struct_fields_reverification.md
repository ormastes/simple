# Seed re-verification: stage2 Cranelift-direct SEGV on nil struct fields (build_signature)

Recipe for re-checking the fix for
`doc/08_tracking/bug/stage2_cranelift_direct_segv_nil_struct_fields_2026-08-24.md`
after the next Rust seed rebuild + stage2 rebuild. Do not edit the bug
record; run this recipe and append the outcome as a new lane addendum
elsewhere if a lane owns one.

## What was fixed

`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`
(`build_signature`) read `sig.params` and `sig.return_type.kind` with no nil
guard. A stage2 self-hosted Cranelift-direct compiler can carry a
`MirSignature` whose fields read back nil at runtime (the stage2
nil-struct-field defect is a *runtime data* property of the produced binary),
and both reads dereference address 0 — the recorded crash was
`mov 0x8(%rbx),%rax; and $~7,%rax; mov (%rax)` on `sig.return_type` with no
guard. The fix fails closed: a nil signature, nil `params`, or nil
`return_type` panics with
`E-BACKEND-CRANELIFT-NIL-SIG: function signature is nil or has nil params/return_type ...`
before any deref, so the worst observable outcome is the loud
`compile error: E-BACKEND-CRANELIFT-NIL-SIG ...` diagnostic on stderr with a
non-zero exit, never a SEGV.

The sibling crash site in the same record (Backtrace B, HIR
`declaration_lowering.lower_function` dereferencing a nil
`get_symbol_type` payload) is already guarded at this tip
(`src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl`: the
`fn_.name != "main"` gate plus the `if val present_fn_sym_type = fn_sym_type`
nil bind before the `.kind` match), so the only live shape was Backtrace A.

## Rebuild and probe (lane p3-sweep4, 2026-11-28)

Scratch caches live under `build/p3cache/nilsegv/` (lane isolation;
`build/p3cache/fresh-seed/simple.exe` is owned by the seed deploy flow — never
overwrite it from a lane build).

```sh
# 1. Scratch-build the Rust seed driver at the tip under test:
cd src/compiler_rust
CC="$HOME/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe" \
  CARGO_TARGET_DIR=$PWD/../../build/p3cache/nilsegv/cargo-target \
  cargo build --release -p simple-driver
cd ../..
SEED=$PWD/build/p3cache/nilsegv/cargo-target/release/simple.exe

# 2. Build the stage2 (self-hosted Cranelift) compiler from the same tree.
#    A plain `native-build --entry-closure` link fails on Windows: the
#    whole-archive module link needs rt_value_eq/rt_process_* (Rust
#    native_all lane) AND the baremetal rt_port_* externs, so name a
#    libsimple_native_all.a directory via --runtime-path, keep the explicit
#    core-c-bootstrap bundle string (it layers the C supplement that owns
#    rt_process_*), and carry runtime_port_io.o via SIMPLE_LINK_OBJECTS.
#    A ready-made runtime archive set from a sibling lane build works as
#    the --runtime-path directory, e.g.
#    build/p3cache/rustauth/replay-target/x86_64-pc-windows-gnullvm/bootstrap
#    (copy the libsimple_*.a files into your own lane dir first).
env SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 \
    SIMPLE_HIR_CACHE_DIR=$PWD/build/p3cache/nilsegv/hir-cache \
    TMPDIR=$PWD/build/p3cache/nilsegv/tmp \
    CC="$HOME/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe" \
    SIMPLE_LINK_OBJECTS=$PWD/build/p3cache/nilsegv/portio/runtime_port_io.o \
  "$SEED" native-build --source src/app \
    --entry src/app/cli/bootstrap_main.spl --entry-closure --strip \
    --threads 24 --timeout 7200 \
    --cache-dir $PWD/build/p3cache/nilsegv/native-cache \
    --runtime-bundle core-c-bootstrap \
    --runtime-path $PWD/build/p3cache/nilsegv/runtime \
    -o $PWD/build/p3cache/nilsegv/stage2/simple.exe

# 3. The doc's deterministic probe (child process — a SEGV cannot kill the lane):
printf 'fn main()\n    print("hi")\n' > build/p3cache/nilsegv/h2.spl
$PWD/build/p3cache/nilsegv/stage2/simple.exe compile \
    build/p3cache/nilsegv/h2.spl --format=smf \
    -o build/p3cache/nilsegv/h2.smf
echo "rc=$?"
```

Expected after the fix on a Linux stage2: when the stage2 binary exhibits
the nil-field data shape, stderr carries
`PANIC: compile error: E-BACKEND-CRANELIFT-NIL-SIG: ...` and rc=1; when the
stage2 data is healthy the probe exits 0 with a valid `.smf`. rc=139
(SEGV) means the defect is live and unabsorbed. On a Windows stage2 the
probe can never reach rc=0 — SMF is ELF-only, so a healthy compile fails
closed at `SMF packaging needs ELF object code, but the backend produced a
COFF object` (rc=1). Either way, any crash exit code is RED.

## Regression spec

`test/01_unit/compiler/70.backend/build_signature_nil_fields_fail_closed_spec.spl`
forges the recorded data shape (a MirSignature with nil params and
return_type) and calls build_signature, driving the probe through
`SIMPLE_BINARY` (default `bin/simple`) with `run --mode=jit` in a child
process (SEGV-proof): RED pre-fix (child SEGV, rc 139 / 0xC0000005), GREEN
post-fix (stderr carries `E-BACKEND-CRANELIFT-NIL-SIG`). No stage2 needed.

```sh
bin/simple test \
  test/01_unit/compiler/70.backend/build_signature_nil_fields_fail_closed_spec.spl
# expect: 1 example, 0 failures
```

## Evidence recorded by the fixing lane (2026-11-28, lane p3-sweep4, Windows)

- Scratch seed (`cargo build --release -p simple-driver` at this tip,
  `build/p3cache/nilsegv/cargo-target/release/simple.exe`) is Cranelift-only;
  no absorber existed (`git log --grep` for the bug id finds no fix).
- Baseline stage2 (pre-fix tree, seed Cranelift native-build of
  `bootstrap_main.spl`, `--runtime-bundle core-c-bootstrap` +
  `--runtime-path` naming a `libsimple_native_all.a` directory +
  `SIMPLE_LINK_OBJECTS` carrying `runtime_port_io.o` for the baremetal
  `rt_port_*` externs the Windows whole-archive link requires): the doc's
  `compile h2.spl --format=smf` probe did NOT SEGV. Codegen ran
  build_signature on h2's module without the nil data shape firing, and the
  run then failed closed at the SMF packager:
  `SMF packaging needs ELF object code, but the backend produced a COFF
  object for this host target` (SMF is ELF-only;
  `src/compiler/80.driver/driver_aot_smf_output.spl`), rc=1. So the
  nil-field *data* shape is not reproducible on a fresh Windows stage2 at
  this tip; the unguarded *code* shape was still live.
- Backtrace B's site (HIR `declaration_lowering.lower_function`) is already
  nil-guarded at this tip (`fn_.name != "main"` + `if val present =
  fn_sym_type` before the `.kind` match,
  `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl`).
- Guard verification (forged-nil probe, `build/p3cache/nilsegv/probe_nil_sig.spl`):
  a MirSignature whose params and return_type are nil, passed to
  build_signature. Pre-fix (`run --mode=jit`, scratch seed): **rc=139
  SEGV** (bash: `Segmentation fault`). Post-fix: stderr carries
  `compile error: E-BACKEND-CRANELIFT-NIL-SIG: function signature is nil or
  has nil params/return_type; refusing to build a Cranelift signature`,
  rc=127, no crash. Regression spec
  `test/01_unit/compiler/70.backend/build_signature_nil_fields_fail_closed_spec.spl`
  green (1 example, 0 failures) on the scratch seed; the probe runs in a
  child process, so a regression SEGV cannot kill the lane.
- Post-fix stage2 rebuilt from the same cache and re-probed with h2.spl:
  no SEGV (fail-closed COFF/ELF diagnostic or clean compile), matching the
  baseline verdict.

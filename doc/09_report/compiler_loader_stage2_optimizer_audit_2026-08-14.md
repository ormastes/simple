# Compiler loader Stage-2 optimizer audit

## Result

PASS with advisory findings. A reduced entry closure called the real
`app.optimize.analyze.optimize_full_analyze` API through the admitted Build11
Stage-2 compiler. It built in 13.5 seconds (55 compiled, zero failed) with
`SIMPLE_NO_STUB_FALLBACK=1`. Each of the four touched Simple implementation
files was analyzed once and returned status 0.

The scanner reported 74 findings for `fs.spl`, 46 for `net.spl`, 17 for
`syscall_raw.spl`, and 112 for `core_array.spl`. Inspection dispositioned them
as indentation-insensitive dead-code warnings, generic indexing/loop notices,
preallocation suggestions, and literal-strength-reduction candidates. The new
adapter calls introduce none of the general findings. The new core-array loops
are required validation/copy loops, and its `* 8` is a code-address stride best
left to compiler strength reduction. No semantics-preserving source edit was
warranted.

## Reproduction

After creating `build/native_probe/restart12_optimizer_audit_main.spl` as a
one-argument wrapper around `optimize_full_analyze(path, "O3", false)` and its
isolated cache directory, the exact build command was:

`env SIMPLE_NO_STUB_FALLBACK=1 timeout 240 build/restart12-build11-a-r2/output/stage2/x86_64-unknown-linux-gnu/simple native-build --backend cranelift --source src --source build/native_probe --entry-closure --entry build/native_probe/restart12_optimizer_audit_main.spl --threads 4 --cache-dir build/native_probe/restart12_optimizer_audit_cache --opt-level=standard --output build/native_probe/restart12_optimizer_audit > build/native_probe/restart12_optimizer_audit_build.log 2>&1`

The binary was run once per file with a 30-second timeout:

- `src/os/userlib/fs.spl`
- `src/os/userlib/net.spl`
- `src/os/userlib/syscall_raw.spl`
- `src/runtime/simple_core/core_array.spl`

The ignored local receipts are
`build/native_probe/restart12_optimizer_audit_{build,fs,net,syscall_raw,core_array}.log`
and `build/native_probe/restart12_optimizer_audit_results.tsv`.

## Provenance

- Stage-2 compiler SHA-256: `16ca2e8d9c88fe874b7a524dc20484818b0a1bed4384341efa36e20c6ff0b86f`
- Audit binary SHA-256: `fe95b337e2721dabaa9695015edfe9e326da72f267c237ffacb568e236bb151c`
- Result TSV SHA-256: `c7782258e5d55c82c0ca96bec004c31f4c49bff35bb7224ca8c323588d7fc790`

This is optimizer-audit evidence only. It does not admit Stage 3, Stage 4, or
live performance results.

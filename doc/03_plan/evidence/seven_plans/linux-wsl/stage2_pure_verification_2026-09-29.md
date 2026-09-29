# WSL Stage 2 in-process verification probe

Status: FAIL, prerequisite remains open. This is not Stage 4 admission.

The existing canonical phase verifier was invoked with
`BOOTSTRAP_STAGE2_TEST_DELEGATE=0`, `--phase=stage2`, `--strategy=normal`,
`--profile=slim`, and a bounded 90-second task timeout. No MC/DC waiver or
test-runner seed delegation was used. Its recorded execution mode is `in-process`.
The native-build route nevertheless calls embedded Rust, as established below;
the execution-mode label does not prove pure-Simple compiler ownership.

Compiler: `/root/simple-bootstrap-main-linux/.simple/storage/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`.
Expected and observed SHA-256:
`59cc994ea150db7ef5ad4b318c06b8c0774e27eb244686f4a5e1189215a331d6`.
The verifier validated the frozen Phase 2 runtime capsule and compiler hash.
Compiler version completed once (exit 0); do not rerun that unchanged criterion.

| Required row | Result |
|---|---|
| Compiler CLI build | TIMEOUT, status 124, 91 seconds, peak RSS 2,528,500 KiB |
| Test runner build | BLOCKED by failed CLI build |
| Compiler-bootstrap, interpreter, loader tests | UNSUPPORTED because no full CLI artifact was built |

The verifier exited 1 with five terminal failures and three unsupported tasks.
This bounded timeout is not proof of an implementation defect or a measured
performance regression; the full CLI may require a longer build. The CLI log
contains no diagnostic that localizes a source failure. No descendant process
from this invocation remained at the final process check.

Work and summary:
`/root/simple-seven-plans-wsl/build/native_probe/stage2-pure-verification/summary.env`.
Retained cache:
`/root/simple-seven-plans-wsl/build/native_probe/stage2-pure-verification-cache`.
Parent log:
`build/native_probe/index-compatibility-tdd/wsl-stage2-pure-verification.log`.
Clang frontend was explicitly selected through `CC` and `SIMPLE_CC` as
`/root/llvm/LLVM-23.1.1-Linux-X64/bin/clang`, with LLVM tools from
`/root/llvm-2311-prefix/bin`. No successful compiler invocation is inferred
from environment selection alone.

Resume owner: parent bootstrap lane. Correct the native-build route before
resuming the blocked runner/tests. Do not promote the
existing Stage 2 admission receipt to passing compiler tests or Stage 4; retain
the failed matrix until the required executable rows actually pass. The original
other-session bootstrap checkout was used as source input, not modified source.
Its HEAD is `bb3f6ab8ab2`; its pre-existing dirty bootstrap and sanity-gate
scripts remain untouched and are not included in this change. This result
does not certify the publication branch's newer source.

## Bounded retry and ownership trace, 2026-09-30

The failed CLI producer was retried once with the retained source, compiler,
runtime capsule and cache, with a 600-second outer timeout. It exited 124.
The version criterion and feature specs were not rerun. At approximately 463
seconds the process was CPU-active at 169% with RSS 2,893,444 KiB; this is a
point observation, not peak RSS. The time receipt was empty after termination.
No cache-hit count or successful artifact admission is claimed.

The log reported unresolved `text.from_char_code` calls and seed aggregate
typing warnings. Read-only source and process inspection established:

- At source HEAD `bb3f6ab8ab2`, `bootstrap_main.spl:668` dispatches native-build.
- Explicit `--entry`, with neither Stage 3 nor Stage 4 marker, selects
  `run_rt_native_build` at line 402; line 243 calls `rt_native_build`.
- `native_build_sffi.rs:692-700` constructs and runs Rust `NativeProjectBuilder`.
- The compiler snapshot defines `rt_native_build`; the live environment had
  `SIMPLE_NO_BOOTSTRAP_DELEGATE=1` but no Stage 3/4 markers. This route does not
  honor that no-delegate flag. No child process is needed for embedded Rust.

Consequently neither this retry nor the original explicit-entry producer is
pure-Simple build evidence. Do not raise the timeout again for this route.
The source-selected pure route takes one positional `.spl` entry, no `--entry`
or `--source`, and no parallel-thread request; it reaches
`compiler_driver_create` / `compiler_driver_run_compile` at lines 485-488.
That route has not been executed here. Preserve the runtime capsule bindings
when preparing it; do not manufacture Stage 3/4 markers to change dispatch.

Retry log: `build/native_probe/index-compatibility-tdd/wsl-cli-resume.log`.
All seven-plan admission and host-completion gates remain open.

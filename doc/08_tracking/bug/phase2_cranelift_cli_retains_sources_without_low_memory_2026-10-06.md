# Phase 2 Cranelift CLI build omits low-memory mode

The production Phase C backend command helper passed `--low-memory` for LLVM but omitted it for Cranelift. `bootstrap_main.spl` accepts that flag for both backends; driver source reclamation depends on it.

On 2026-10-06 the isolated Linux Cranelift bootstrap compiled 1,203 Phase 2 modules with zero failures and passed both bootstrap-mode frontend sanity probes, including real positional Hello compilation and execution. Its exact producer SHA-256 was `33517e08dc520f7016ccc228a973f0b65de069b12aead83885168d6afb18a69d`, source `c6e6449f9d6aadec1ed545851b338ebfe1c89a7b`.

The subsequent sequential CLI build stopped at HIR 708 / 2,618, with zero module failures. The outer resource guard exited 88: `rss-cap-exceeded`, peak 5,862,244 KiB versus limit 5,859,375 KiB, `quiescent=1`. No CLI artifact or test-runner build was produced. Raw evidence is retained under `/tmp/simple-cranelift-adhoc-20261006/`, including `build.rss.env` and `stage2-compiler-tests/x86_64-unknown-linux-gnu/verification/logs/compiler_cli_build.log`.

The helper now passes the existing low-memory option for Cranelift as well. The shell contract regression checks both backend argv and rejection of an unsupported backend. This proves the launch contract only; a fresh native CLI build must still prove the memory failure is resolved. Qualification remains pending.

This issue is distinct from provisional Phase 3 cold source-inventory hashing, which exceeded the same cap before CompilerDriver creation even with `--low-memory`. Those failed attempts and the bounded GDB stack remain in `/tmp/simple-cranelift-phase3-20261006/failure.md`. Do not claim this helper change resolves that separate boundary.

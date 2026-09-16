# Strict stage3 self-host body failures

A strict cached stage2 linked, but contained 62 uppercase weak definitions and
was not acceptable evidence. Stage3 invalidated the compiler-dependent objects,
recompiled the 616-file bootstrap closure, and failed closed on 50 files rather
than emitting body stubs.

The failures group into existing owner defects: ambiguous/misresolved methods,
Cranelift type verification, unsupported multi-register returns and parallel
operators, missing GPU intrinsics, one capability violation, and one relative
import failure. Evidence is retained in
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

The bootstrap cache context now fingerprints strict stub policy so an older
stub-permitting cache cannot masquerade as a strict stage2 success. Fix the
grouped compiler owners with focused regressions before the next strict run.

Most failing files are unrelated to `bootstrap_main` (GPU, benchmark examples,
MCP experiments, legacy interpreter, and networking). A focused collision
fixture proved why: `use lib.shared.{value}` from `src/app/main.spl` discovers
both `src/lib/shared.spl` and the wrong relative
`src/app/lib/shared.spl`. Restricting discovery to one `src` resolver did not
fix it because that resolver still prefers the relative candidate. The failed
experiment was removed after the three-cycle cap. Next fix the per-import rule:
top-level project namespaces resolve from project `src`; only genuinely local
module paths may resolve relative to the importing file.

The focused `lib.*` collision regression now passes, but a fresh clean strict
bootstrap still failed stage3 on 53 unrelated files. Discovery continues to
union every resolver's result and then independently add every filesystem
fallback match. The next owner change must resolve each import atomically:
first successful resolver wins; filesystem fallback runs only when every
resolver misses and stops at its first deterministic match. Keep explicit
source roots as indexes, never as additional compile sets.

Atomic per-import discovery now passes its collision regression. A new clean
cycle produced stage2 (603 compiled, 0 failed), then strict stage3 failed on
144 files. The wrapper incorrectly continued into seed-fallback stage4, whose
orphaned worker consumed one core for 83 minutes without producing a cache
object, final binary, or fresh terminal output. This was a nonconverging
compiler worker after a rejected stage, not terminal I/O deadlock.

`bootstrap-from-scratch.sh` now fails immediately after stage2/stage3 failure
when `SIMPLE_NO_STUB_FALLBACK=1` is set, so a strict run cannot enter that
fallback stage4 again. The remaining work is the grouped stage3 compiler-body
failures; do not diagnose them through seed-fallback output.

The next focused closure gate exposed package-hub fan-out rather than 144
independent body defects. Reachable driver leaves used `compiler.driver` and
the SMF getter used `app.io`; the latter initializer imports CLI, JIT, test,
CUDA, and Vulkan modules. These imports now name their concrete owners. The
bootstrap closure regression passes (`1 passed; 0 failed`) and excludes the
driver initializer, `app/llm_caret`, and `app/leak_finder`. If a later strict
stage3 still visits those application trees, capture discovery trace evidence:
their bodies are not legitimate bootstrap dependencies and must not be fixed
merely to make the oversized closure compile.

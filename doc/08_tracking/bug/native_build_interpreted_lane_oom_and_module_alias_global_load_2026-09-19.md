# Seed native-build interpreted-driver lane OOM + module-alias GlobalLoad regression (2026-09-19)

## Symptom (beta.13 release run, both blocking legs reached for the first time)

After the SCV-freeze wall fell (de-symlink PR #1111), the v1.0.0-beta.13
release run failed in the seed `native-build` step on every platform:

- **windows-x86_64**: hard segfault ~5m45s into the step (job 105839324388)
- **darwin-arm64**: `Killed: 9` (jetsam OOM) ~13 min in (job 105839324392)
- **linux-x86_64**: external runner shutdown (9th occurrence of the
  infra-level kill; see the standing escalation)

Local repro of the exact CI command showed RSS climbing monotonically:
15.7 GB working set / ~50 GB paged at 25 min and still growing.

## Root cause (two distinct bugs)

### 1. The workload runs in the interpreted Simple driver, not the Rust pipeline

`seed.exe native-build` dispatches to the interpreted
`native_build_main.spl` driver unless `SIMPLE_NATIVE_BUILD_RUST=1` is set
(`src/compiler_rust/driver/src/main.rs:168-171`). The interpreted lane
tree-walks a ~1,990-function driver while retaining the whole compiler
import graph — documented in-repo as pathological
(`driver/src/cli/commands/misc_commands.rs:877-891`, 28.4 GB RSS). The
Rust `native_project` pipeline with the same command peaks at
**~1.2–1.6 GB flat** and compiles all 869 modules in ~6–8 min
(threads=2). The repo's own `bootstrap-from-scratch.sh` already sets
`SIMPLE_NATIVE_BUILD_RUST=1`; the release/build-binaries workflows did not.

### 2. `llvm_native_link.spl` module-alias call breaks the Rust lane's codegen

Commit `1df509a0ce5` (in the beta.13 tag) changed the orchestrator import
from a function import to a module alias:

```
use compiler.backend.backend.llvm_native_link_orchestrator as llvm_native_link_orchestrator
... llvm_native_link_orchestrator.link_llvm_native(...)
```

The interpreted lane resolves module aliases lazily; the Rust codegen lane
lowers the qualifier to `GlobalLoad llvm_native_link_orchestrator`, which is
"not a global, function, const-data name, or import" for this shape —
`codegen: 1 function body/bodies failed to compile: [link_llvm_native]`
(868/869 modules otherwise OK). Function imports via `use mod.{fn as alias}`
are the supported path; the file's local wrapper `link_llvm_native` only
existed to shadow the imported name.

## Fix (beta.14)

1. `SIMPLE_NATIVE_BUILD_RUST=1` added to the five full-tree seed
   native-build steps: release.yml (linux :335, macOS :407, windows :520)
   and build-binaries.yml Stage 2 (:196, :275). MCP package steps keep the
   interpreted lane (small closure, currently works).
2. `llvm_native_link.spl`: import
   `{link_llvm_native as orchestrator_link_llvm_native}` and call the alias
   directly — semantics unchanged, codegen-supported shape.
3. Rust pipeline memory hardening (defense in depth, ~25% peak cut,
   identical per-module compile outcomes vs pristine):
   - `compiler.rs:731-742,761` — whole-graph struct/enum/owner maps shared
     via `Arc::clone` instead of per-module deep clones (O(graph²) removed)
   - `compiler.rs` — `build_suffix_index` hoisted to once per compile phase
   - sources shared as `Arc<str>` through to_compile/worker args
   - `module_cache.rs` — parsed-source cache bound to 256 per compile
     worker (env `SIMPLE_PARSED_SOURCE_CACHE_MAX` overrides)

## Evidence

- Local full-closure runs, exact CI command + env, fixed seed: peak
  ~1.20 GB flat (vs ~1.61 GB pristine, vs 41.5 GB interpreted lane, vs
  ~50 GB+ unfixed-interpreted local curve).
- `cargo test -p simple-compiler module_cache`: 10/10 pass.
- Full closure (869 modules) compiles; stage1 binary produced;
  `--version` and `-c "print 42"` verified after fix 2.

## Addendum: local link-stub pitfall (machine-specific, not a repo bug)

Local validation initially failed at the main-stub compile because this
machine's MSYS2 mingw64 g++ is incomplete (`cc1plus.exe` missing; exits 1
silently). The Rust lane's C++ compiler discovery honors the **`CXX`** env
var (`common/src/platform/cc_detect.rs:95`), not `SIMPLE_CC` (Simple lane).
`CXX=C:/dev/tool/llvm-mingw-20231128-ucrt-x86_64/bin/clang++.exe` works.
CI's GitHub images ship complete mingw toolchains, so this does not affect
the release legs.

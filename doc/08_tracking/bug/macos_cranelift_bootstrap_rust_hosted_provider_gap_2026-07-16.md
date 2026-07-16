# macOS Cranelift bootstrap: Stage 2 rust-hosted provider link gap (2026-07-16)

## Scope

Apple Silicon (`aarch64-apple-darwin`), strict full bootstrap, Cranelift
backend, dynload process mode.

## Reproduction

```sh
env SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --backend=cranelift --mode=dynload --no-mcp --jobs=half
```

## Result

The refreshed Rust seed successfully enters Stage 2 and compiles the entry
closure. The final hosted link fails with 171 undefined symbols. The set mixes
runtime lifecycle (`__simple_runtime_init`, `__simple_runtime_shutdown`),
platform graphics (`MTLCreateSystemDefaultDevice`), database, CUDA, stdin,
time, UUID, volatile-memory, value-kind, and imported Simple trait helpers.

Authoritative evidence:

- `build/native_probe/macos_full_bootstrap_cycle3_cranelift.log`
- `build/bootstrap/logs/aarch64-apple-darwin/stage2-native-build.log`

The strict fallback guard worked: no Stage 2 binary was admitted or deployed.

## Boundary

This is separate from the Rust-seed LLVM `mcall_direct` arity defect. Cranelift
avoids that code-generation failure and reaches the linker, where the
`rust-hosted` bundle plus whole-archive selection does not provide the complete
entry-closure ABI on macOS.

## Required fix

Make runtime-provider composition explicit for the Stage 2 `rust-hosted`
bundle. The selected provider set must cover every retained entry-closure
symbol, or entry-closure discovery must exclude optional platform/provider
modules that cannot be reached by `bootstrap_main`. Add an Apple Silicon link
contract that fails with the grouped missing-provider owners before invoking
the system linker.

## Acceptance

1. The reproduction completes strict Stage 2 and Stage 3 sanity.
2. No seed fallback is used.
3. The resulting binary has no unresolved runtime/provider symbols.
4. The hash-bound pure-runtime redeploy gate passes before replacing
   `bin/release/aarch64-apple-darwin-macho/simple`.

## Stage 2/3 resolution evidence (2026-07-16)

The provider list was mostly a reachability artifact. macOS force-loaded every
entry-closure object but did not request section dead stripping, so references
from unreachable optional functions remained link requirements. Adding
`-Wl,-dead_strip` reduced the strict missing set from 171 symbols to the two
genuinely live entry hooks. Native-all now directly exports
`__simple_runtime_init` and `__simple_runtime_shutdown`, and macOS host
frameworks are selected from the actual native-all choice rather than a second
global archive lookup.

Evidence:

- focused Mach-O archive probe: force-load fails without dead stripping and
  passes with it;
- `macos_native_all_link_args_dead_strip_and_retain_metal_support`: PASS;
- `hosted_runtime_lifecycle_hooks_are_callable`: PASS;
- strict Stage 2: 711 objects (`3 compiled, 708 cached`), zero failed, sanity
  PASS, SHA-256
  `a320dfd6644ba10560e05e88c9d354fb91e68326275f825fc0c1688b28ea9741`;
- strict Stage 3 self-host: 711 compiled, zero failed, sanity PASS, SHA-256
  `d22da42d15916a8e88822617ca9e8cb573527aaf4005a6b47624c4100b18c5e4`.

Stage 2/3 are resolved. Acceptance item 4 remains open until a full CLI is
produced and passes the redeploy gate; no deployed runtime was replaced here.

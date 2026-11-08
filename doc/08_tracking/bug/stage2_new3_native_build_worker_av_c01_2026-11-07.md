# stage2_new3 native-build worker AV on c01 (2026-11-07)

**Status:** fix-implemented-verification-pending, P1. Blocks retiring the frozen stage2.
Native verification = rebuild the seed from a tip containing the fix, rebuild stage2 with it,
rerun `c01` (and `hello`/`var`) through `run_case_s2new_mf8.ps1`.

## Repro
- Binary: `C:/dev/p3new/stage2new/stage2_new3.exe` (26,523,136 B, built 2026-11-07 17:32). Built from
  `7fdd36aa490` + #7506 + #7541 + the workaround-removal commit `0bccd872d15`, with the
  64 MiB stack patch.
- Command: `pwsh C:/dev/p3new/s3sanity/run_case_s2new_mf8.ps1 -Name c01 -Bin <stage2_new3.exe>`
- Result: parse, HIR, AOP weave and native_cache all finish. Then:
  `phase=native_compile current=test.s3sanity.c01` ->
  `native-build worker terminated with Windows native status 0xC0000005 (access violation)`.
  bootstrap-error-count is 0 at every point. No `rejected invalid array handle` line is printed.
  hello fails the same way; var produced no log.
- Earlier evidence: `stage2_new.exe` (rebuild #1) AV'd on c01 after `rejected invalid array handle`,
  root-caused and fixed in #7541. This AV is a new site, in codegen/native_compile.

## Root cause (2026-11-08, lldb attached to the worker child by PID)

```
Exception 0xc0000005 at StrictSdnReaderV1.byte_at + 19: Access violation reading location 0x48
frame #0 lib__common__sdn__strict_v1__StrictSdnReaderV1.byte_at
frame #1 compiler__driver__driver_build__incremental__incremental_fingerprint_digest_valid_v1
frame #2 compiler__driver__driver_build__incremental__FileFingerprint.from_file
frame #3 compiler__driver__driver_aot_native_output___compile_frozen_module_capsule_prefetched_v1
frame #4 CompilerDriver._compile_to_native_with_backend_session
```

The stage2 source (`7fdd36aa490`) had

```simple
pub fn incremental_fingerprint_digest_valid_v1(digest_opt: text?) -> bool:
    if digest_opt == nil: return false
    val digest = digest_opt.unwrap()
    ...
        val byte = digest.byte_at(index) as i64
```

The **Rust seed** typed `digest_opt.unwrap()` as ANY: `text?` reaches the HIR builtin-method
dispatcher with a STRING receiver (the text slot is itself nullable), and the `unwrap` arm only
handled named-struct/enum pointees, Option/Result enums, BoxInt scalars and `Char?`. With `digest`
typed ANY, MIR could not route `digest.byte_at(index)` to `rt_string_byte_at` and left a
name-dispatched `byte_at` call; the LLVM codegen suffix-match fallback (keyed on leaf name + arity,
owner unknown for an ANY receiver) bound it to the only same-leaf/same-arity method in the link
closure, `StrictSdnReaderV1.byte_at(offset)`, which dereferenced the text pointer as a class
(`self.bytes` at +0x48). The disassembly of the stage2 function shows the direct call to the mangled
`StrictSdnReaderV1.byte_at` symbol.

- Not caused by the workaround removal `0bccd872d15` (it never touched this site).
- The release tip already rewrote the site to `digest: text` (`df6d91dc6a0`), which is why a
  stage2 rebuilt from the current tip would not hit *this* instance; the seed bug stays live for
  every other `x = opt_text.unwrap(); x.<text-method>()` whose leaf collides with a user method.
- Minimal seed repro (seed from `7fdd36aa490`, `native-build --backend llvm`): a single file with a
  class `fn byte_at(offset: i64)` plus `fn f(d: text?)` doing `val s = d.unwrap(); s.byte_at(i)`
  exits 139 (SEGV); with `d: text` it prints PASS.

## Fix
- `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs` (`lower_builtin_method_call`, `unwrap`
  arm): a STRING receiver or a source Optional over STRING lowers to the builtin
  `rt_unwrap_or_trap` typed STRING, so the bound local is STRING and every chained text method is
  routed to its runtime owner in MIR.
- Regression test: `src/compiler_rust/compiler/src/hir/lower/tests/seed_regression_tests.rs`
  `stage2_text_optional_unwrap_keeps_string_type_for_byte_at`.
- Native smoke fixture: `test/04_smoke/native_text_optional_unwrap_byte_at.spl` (expected stdout
  `PASS text_optional_unwrap_byte_at`; the seed built from a pre-fix tip exits 139 on it).

## Decision
Phase 2 rebuilds stay paused until the seed carrying this fix is rebuilt. Phase 3 continues on the
frozen stage2 lineage (`s3_fable61` gate PASS). The workaround-removal PR is no longer implicated.

# Site 13: a cross-module call is emitted fully qualified while its definition is emitted bare, so Stage 2 fails to LINK

- **Status:** OPEN (2026-09-13)
- **Lane:** BOOT-12, measured on the Stage-2 candidate this lane built,
  `build/bootstrap-boot12a/stage2-rejected/aarch64-unknown-linux-gnu/simple`,
  sha256 `d49850e28673657d80be…`, 152285712 B (pin
  `scratchpad/boot12/pin/cand.boot12a.stage2`).
- **Severity:** the Stage-2 admission blocker that succeeds site 12
  (`stage2_capsule_source_identity_is_sha256_of_empty_2026-09-13.md`). It is not
  caused by that fix — it was MASKED by it: capsule collection failed before the
  link step ever ran, so the link could not report anything.

## The bootstrap verdict (canonical `--stop-after-stage2`, `build/bootstrap-boot12a`)

```
| error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
| error: in-process native-build: LLVM native linking failed: Linking failed: cc linking failed: ld.lld: error: undefined symbol: compiler.common.module_path_naming.module_logical_name_from_path
| collect2: error: ld returned 1 exit status
PASS — 1 check(s), stage stage2 failed (exit 3) and said why
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Zero `native-capsule-source-mutated` and zero `frozen-identity-absent…` lines in
that same `stage2-receiver.log`, so site 12 is closed and this is what is left.

## Measured cause — the two sides disagree on the symbol name (and on the type)

Standalone repro, 80 s, same candidate, the redeploy gate's own fixture
(`scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl`, which
is a 12-line file whose whole job is `use compiler.common.module_path_naming.{module_logical_name_from_path}`):

```sh
CAND=scratchpad/boot12/pin/cand.boot12a.stage2 \
  sh scratchpad/boot12/fxrun.sh scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl gatefx1
```

Both modules compile and both objects reach the linker —
`phase=native_cache … done=2 total=2 succeeded=2 failed=0`, then
`phase=link … unit_kind=objects done=2 total=2 succeeded=2` — and the link still
fails, because the retained IR names the same function two different ways:

| module | line |
|---|---|
| provider (`src/compiler/common/module_path_naming.spl`) | `define ptr @module_logical_name_from_path(ptr %l0) nounwind {` |
| consumer (the fixture) | `%l1 = call ptr @compiler.common.module_path_naming.module_logical_name_from_path(ptr %l0)` |
| consumer | `declare i64 @compiler.common.module_path_naming.module_logical_name_from_path(...)` |

The definition is emitted **bare**; the reference is emitted **module-qualified**.
`ld.lld` is right: nothing defines the qualified name. Note a SECOND disagreement
on the same line — the consumer declares the return as `i64 (...)` varargs while
the definition returns `ptr` — so even a name fix must make the declared
signature agree, or the call will misread the result.

The provider's other two functions are emitted bare as well
(`@_module_path_naming_strip_numbered_dirs`, `@_module_path_naming_text_index_of`),
so this is the rule the provider follows, not a one-symbol slip.

Raw evidence: `scratchpad/boot12/fxrun/gatefx1/{build.log,keep/module.*.ll}`,
`build/bootstrap-boot12a/stage3/aarch64-unknown-linux-gnu/stage2-receiver.log`.

## Why it appears only now

Site 12 rejected every capsule at collection, which is upstream of object
emission and linking, so no `--stop-after-stage2` run has reached the link step
for this closure before. The same fixture under the previous candidate
(`ba3c25f30d76c9a8…`) exits at `native-capsule-source-mutated` with no linker
line at all.

# Cocoa standalone provider: extraction prerequisite, admission pending

Date: 2026-09-23. Status: diagnostic provider slice; production demand loading
is **not complete**. Base P0: `bbdc5555836247b07d98be246d440ae3bafc1d01`.
Preserves ownership patches `d832604d7a2` and `44d17634e3f` unchanged via
cherry-picks `22dab172244` and `a3f1f7e07ba` respectively; the latter is this
slice's immediate parent. Stable patch IDs match both originals.

`sh scripts/build/build_spl_cocoa.shs` builds `build/sffi/libspl_cocoa.dylib`
and `libspl_cocoa.producer.txt`. The ad-hoc signature and producer receipt
identify a diagnostic artifact; neither admits it for production execution.
The receipt records source/artifact SHA-256, compiler/version, Objective-C
lowering flags, architecture, install name, observed dependency listing/hash
and code signature. Dependency listing equality is not a dependency lock.

The provider exports eleven existing scalar/opaque-handle operations and
`rt_cocoa_window_new_raw(i64, i64, const char *, i64)`. Its borrowed title is
copied before return, capped at 1,048,576 bytes, and need not be NUL-terminated.
Negative/oversize/null-nonempty/embedded-NUL titles fail before window creation.
Zero length retains the legacy `untitled` default. There are no tagged value
decoder imports. C `bool` signatures remain unchanged. Successful diagnostic
mapping is retained for process lifetime; resource close does not prove unload.

The default compatibility build still exports `rt_cocoa_window_new` and keeps
current runtime placement/framework linkage. That path preserves invalid-size
and main-thread rejection before decoding tagged text. Existing callers are
not switched to a permanently failing trampoline.

## Evidence

macOS arm64 / Apple clang 17 diagnostic checks:

Independent Astra code review accepted this diagnostic scope before commit;
review did not rerun runtime checks or grant production admission.

- Built and verified the signed standalone Mach-O; exactly twelve operation
  exports and no Simple/tagged-string undefined dependency.
- Native dynamic harness starts without AppKit or the provider mapped, then
  explicitly loads the diagnostic artifact. Offscreen create/fill/read/free
  and double-free rejection pass through its actual exported typed functions.
- The same harness with `--window` creates, presents, pumps events and closes
  three real windows using a bounded non-NUL-terminated title.
- Raw-title fixture verifies rejection bounds, independent copied storage and
  default title. Non-macOS preprocessor build executes all twelve sentinels.
- Existing frame ownership fixture passes 100 replacements, three allocation
  failure paths and teardown. Existing legacy window ownership fixture passes
  normal and off-main-close modes, twenty window lifetimes each.

Commands (run against this worktree, no Rust seed or whole runtime rebuild):

```sh
sh scripts/build/build_spl_cocoa.shs
clang -std=c11 -Wall -Wextra -Werror -DSIMPLE_COCOA_PROVIDER_ONLY src/runtime/test/cocoa_dynload_owner_selfcheck.c -o build/sffi/cocoa-provider-selfcheck
build/sffi/cocoa-provider-selfcheck "$PWD/build/sffi/libspl_cocoa.dylib" --window
clang -fno-objc-arc -framework Cocoa -Werror test/01_unit/runtime/cocoa_raw_title_test.m -o build/sffi/cocoa-raw-title-test
build/sffi/cocoa-raw-title-test
clang -U__APPLE__ -std=c11 -Wall -Wextra -Werror test/01_unit/runtime/cocoa_provider_nonmac_test.c -o build/sffi/cocoa-provider-nonmac-test
build/sffi/cocoa-provider-nonmac-test
```

## Remaining gate

The canonical `ExactArtifactDynLib` supports sealed Linux snapshots; Darwin
currently rejects exact admission. P0 capsule metadata only admits the main
runtime dylib and supplies no Cocoa retained-handle bridge. Generic checked
dlopen, path/pre-post SHA, environment paths and mutable owner-only permissions
cannot substitute for exact-byte constructor admission.

The separate authority lane must qualify the Darwin mapping primitive and
optional artifact/dependency receipt before core typed lazy trampolines can
replace existing linkage. Then add the no-GC consumer owner, full-table
publication, main-thread guard, generation/rejection cache and process-lifetime
pin; remove AppKit/Cocoa from mandatory core linkage. Production absent-provider,
identity/ABI/dependency mutation rejection, compiled Simple facade, unchanged
core/provider-only mutation, and startup/RSS/hot-dispatch budgets remain pending.
Native fixture success here is not compiled Simple GUI or production admission
evidence and does not resolve the independent implicit-receiver compiler bug.

# mingw link: liboldnames only comes from MSVC-ABI inputs (2026-11-02)

- No stage4/native-build link emits `-loldnames`: scripts/bootstrap/p3-manual-link-stage3.shs:168,
  native_all_support.spl `native_all_gnu_support_args` ("windows-mingw"),
  native_linking.spl `native_runtime_archive_inputs_for_platform` (libsimple_*.a unless msvc).
- clang adds `-lmoldname` (shipped by llvm-mingw). Neither llvm-mingw nor msys64 clang64 ships
  `liboldnames.a`; do not add a host-config path for it.
- Root cause of `undefined unlink/close/open/read/write/mkdir/rmdir`: `/DEFAULTLIB:oldnames.lib`
  (and libcmt) directives embedded in MSVC-ABI objects, e.g. build/simple-core/simple_runtime.lib.
  Fix = build the runtime with `--target=x86_64-w64-windows-gnu`; never feed MSVC-ABI archives to a GNU link.
- Guard: test/01_unit/compiler/linker/windows_mingw_no_oldnames_spec.spl.

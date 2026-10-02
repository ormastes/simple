# MSVC runtime archive SDK import closure

Windows Phase2 diagnostic4 compiled two modules and reused 1,115, then failed
linking 21 imports from the debug native-all archive. The missing families
were `RoOriginateErrorW`, `VariantTo*`, and `PropVariantTo*`.

The MSVC `PlatformLinkConfig::windows()` library list omitted `propsys` and
`runtimeobject`, although the existing MinGW list includes both. Add these
SDK import libraries to the MSVC list. This changes no frozen bootstrap
source or running artifact; a rebuilt driver is required to consume it.

## Focused verification

A three-call C object imports `RoOriginateErrorW`, `VariantToInt32`, and
`PropVariantToInt32`. Standalone LLVM 23.1.1 compiled the object successfully.
`lld-link /nodefaultlib /entry:probe /subsystem:console /machine:x64` failed
without the two libraries (exit 1) and linked successfully with Windows SDK
10.0.26100.0 x64 `propsys.lib` and `runtimeobject.lib` (exit 0). The probe was
linked only, not executed; its null arguments are not runtime API tests.

Source, object and logs are retained at
`C:/Users/ormas/AppData/Local/Temp/msvc-sdk-link-closure-20261002/`.
The initial MSYS compiler on PATH failed to start with status -1073741515;
that tool startup failure is distinct from the standalone LLVM link test.

This verifies the representative missing SDK symbol closure, not all 21
imports, a rebuilt Rust driver, or the complete Phase2/Phase3/Phase4 build.
The parallel bootstrap lane separately uses the canonical bootstrap profile
with its retained caches. Full driver/bootstrap verification remains open.

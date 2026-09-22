# Native debug enum ownership regression

`main.spl` exercises all 19 variants of `DebugExecutionMode`,
`DebugTransportKind`, and `Architecture` through the production Simple modules.
Exit 0 must include `PASS: 19 debug enum names use their Simple owners`.
The four architecture variants omitted by the removed C shim are included.

Use an explicitly admitted Stage2/Stage3 producer or a qualified release CLI,
with its frozen runtime capsule, isolated cache, and `SIMPLE_NO_STUB_FALLBACK=1`:

```sh
"$compiler" native-build --runtime-bundle host-gpu --runtime-path "$runtime" \
  --source src/lib --source test/fixtures/native/debug_enum_owner --entry-closure \
  --entry test/fixtures/native/debug_enum_owner/main.spl --threads 1 \
  --cache-dir build/native_probe/debug_enum_owner/cache \
  --output build/native_probe/debug_enum_owner/debug_enum_owner
build/native_probe/debug_enum_owner/debug_enum_owner
```

This fixture proves behavior. Its source root yields `src__lib__` method names,
so it alone does **not** reproduce the MCP `lib__` duplicate-symbol failure.
`test/01_unit/runtime/debug_enum_symbol_ownership_spec.spl` separately guards
against C redefinitions of those exact mangled names; run it only with a
qualified test runner.

For the exact link regression, retain the failed native MCP build's object
directory. Select its generated session-model/types objects using `nm` rather
than assuming their module numbers remain stable. The 2026-09-23 Phase2 build
used `mod_85.o` and `mod_86.o`. With their original `runtime_native.o`, Apple
`ld -r -arch arm64` fails with precisely the three duplicate symbols. Compile
the current `src/runtime/runtime_native.c` with the recorded core-C flags and
substitute that object in the same link; it must succeed. `nm -gU` must show
one strong definition of each method in the combined object, none in the new
runtime object, and an old/new runtime export delta of exactly those methods.
Do not use weak symbols or duplicate-definition suppression.

The retained-object reproduction and full MCP relink are documented in
`doc/08_tracking/bug/macos_mcp_debug_enum_duplicate_symbols_2026-09-23.md`.

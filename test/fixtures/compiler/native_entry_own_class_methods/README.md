# native_entry_own_class_methods (tag: native, stage3)

Repro for `doc/08_tracking/bug/native_build_entry_module_loses_own_class_methods_multimodule_2026-08-17.md`.
An entry module that has any `use` import loses its own class methods under
multi-module native-build.

    cd test/fixtures/compiler/native_entry_own_class_methods
    <stage3>/simple native-build --entry main.spl -o probe && ./probe

PASS = `w.n=42`. Known-bad: `MIR lowering error: unresolved method call: bump`.
Control: drop the `use` line and inline 41, and it passes.

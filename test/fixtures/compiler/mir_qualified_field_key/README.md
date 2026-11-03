# mir_qualified_field_key (tag: native, stage3)

Repro for `doc/08_tracking/bug/mir_qualified_field_key_namespace_mismatch_2026-08-08.md`.
Two modules define `Config` with different layouts; the importer constructs
mod_b's `Config` and reads `gamma`.

    cd test/fixtures/compiler/mir_qualified_field_key
    <stage3>/simple native-build --entry main.spl -o probe && ./probe

PASS = `direct.gamma=888`. Known-bad output: `direct.gamma=0`, because the
importer resolves the bare `Config` key to mod_a's layout. Interpreter runs
pass, so this fixture only discriminates under native codegen.

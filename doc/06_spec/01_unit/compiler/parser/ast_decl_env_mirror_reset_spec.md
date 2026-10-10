# Legacy direct declaration mirrors reset

Status: **UNEXECUTED**. This authored companion records the exact executable scenarios and assertions; it is not generated execution evidence or a verify PASS.

Source: `test/01_unit/compiler/parser/ast_decl_env_mirror_reset_spec.spl` at `d208b224254e6030e3365ca16df0673fd8c5d564`.

Two examples explicitly select legacy declaration mode and restore its prior environment value before assertions. The first checks real function/struct/import writers populated the four direct keys, then reset removed them. The second restores a real flat-pool snapshot after another import occupied the same declaration slot; it checks prior consumer names and restored provider names exactly. These are source-owned reset assertions, not full compiler or phase admission.

Native reset verification and candidate control results are separate, pending evidence. No successful execution is inferred from the six-line production repair.

## Exact executable spec

The complete source is reproduced to retain helper setup, environment restoration, real assertions and fail-fast branches.

```simple
# UNEXECUTED: requires a producer containing the direct-key reset repair.
use std.spec.*
use std.nogc_sync_mut.io_runtime.{env_get_nullable, env_set, env_remove_process}
use compiler.core.ast.*
use compiler.frontend.core._Ast.decl_nodes.*
use compiler.frontend._FlatAstBridge.module_assembly.{flat_pools_dump_all, flat_pools_restore_all}

fn restore_decl_test_env(key: text, saved: text?):
    if val value = saved:
        env_set(key, value)
    else:
        env_remove_process(key)

describe "legacy direct declaration mirrors reset":
    it "removes every direct body field and import key written by declarations":
        step("Write real declarations in legacy mode and retire their mirrors")
        val saved = env_get_nullable("SIMPLE_NATIVE_ARENA_DECLS")
        env_set("SIMPLE_NATIVE_ARENA_DECLS", "0")
        ast_reset()
        val fn_idx = decl_fn("old", [], [], 0, [7], 0, [], 0)
        val struct_idx = decl_struct_def("Old", ["field"], [3], [], [], 0)
        val import_idx = decl_use_import("old.provider", ["Pattern"], 0)
        val keys = [ast_decl_body_key(fn_idx), ast_decl_field_names_key(struct_idx), ast_decl_field_types_key(struct_idx), ast_decl_imports_key(import_idx)]
        var written = true
        for key in keys:
            if env_get_nullable(key) == nil:
                written = false
        ast_reset()
        var removed = true
        for key in keys:
            if env_get_nullable(key) != nil:
                removed = false
        restore_decl_test_env("SIMPLE_NATIVE_ARENA_DECLS", saved)
        ast_reset()
        expect(written).to_be(true)
        expect(removed).to_be(true)

    it "reads restored provider import names instead of the preceding consumer mirror":
        step("Restore a real flat-pool snapshot after a different import used its slot")
        val saved = env_get_nullable("SIMPLE_NATIVE_ARENA_DECLS")
        env_set("SIMPLE_NATIVE_ARENA_DECLS", "0")
        ast_reset()
        val provider_idx = decl_use_import("provider.span", ["Span"], 0)
        val snapshot = flat_pools_dump_all()
        ast_reset()
        val consumer_idx = decl_use_import("consumer.pattern", ["Pattern", "PatternKind"], 0)
        val previous = decl_get_imports(consumer_idx)
        ast_reset()
        val restored = flat_pools_restore_all(snapshot)
        val current = decl_get_imports(provider_idx)
        restore_decl_test_env("SIMPLE_NATIVE_ARENA_DECLS", saved)
        ast_reset()
        expect(consumer_idx).to_equal(provider_idx)
        expect(previous).to_equal(["Pattern", "PatternKind"])
        expect(restored).to_be(true)
        expect(current).to_equal(["Span"])
```

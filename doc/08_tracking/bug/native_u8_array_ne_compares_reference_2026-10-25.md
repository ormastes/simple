# Native `[u8] != [u8]` compares by reference, not contents

Found 2026-10-25 while proving the convnodes retained_file workaround natively.

Compiler: Stage 2 p2shard-17 (`S/r27/stage2-simple`), aarch64, cranelift,
`native-build --runtime-bundle core-c-bootstrap`.

Repro (tiny entry, native):

```
val a: [u8] = [1u8, 2u8]
val b: [u8] = [1u8, 2u8]
print "lit_ne={a != b}"        # prints true; expected false
```

Two `retained_file_open` handles on the same file gave identity arrays with
equal length (56) and 0 differing elements, yet `f1.identity != f2.identity`
was true. Consequence: `retained_file_identity_unchanged` (and
`retained_file_unchanged`) always returned `Err("SCVDB_FILE_CHANGED")` in
native builds.

Workaround (`@workaround` in `src/lib/nogc_sync_mut/io/retained_file.spl`):
`_retained_bytes_equal` compares element-wise. Verified: the native probe then
returns `Ok(true)`.

Open compiler bug: array `==`/`!=` lowering must compare contents (length +
elements), matching interpreter semantics. Not fixed here; per policy it takes
effect when the Phase 3 compiler rebuilds itself.

## 2026-11-04 triage (n88b): fix already landed

Root fix: `ff9555ded33` "fix(mir): array ==/!= compares contents via rt_native_eq, not handle identity (A1)"
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, `bin_is_array_eq` arm; its comment cites this bug).
Status: fix-implemented-verification-pending. Native repro (needs a stage3 built after ff9555ded33):
`bin/simple native-build` the 3-line entry above; expected `lit_ne=false`. The `_retained_bytes_equal`
workaround in `retained_file.spl` may be retired after that passes.

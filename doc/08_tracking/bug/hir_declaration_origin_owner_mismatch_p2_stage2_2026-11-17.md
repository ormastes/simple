# HIR declaration origin owner mismatch in p2 Stage 2 (2026-11-17)

Status: open (investigation). The diagnostic has landed. The root cause is not confirmed.

Related: `stage2_sanity_origin_check_p2_add_2026-11-17.md` landed a tagged
workaround on `release/1.0.0`. It skips the binding when any side is an SCV
snapshot path. The diagnostic message below also applies to the mismatches
that workaround still lets through.

## Symptom
The p2 Stage 2 sanity build of `src/compiler/bootstrap_admission/p2_add.spl`
reported 27 errors with the message `source declaration origin mismatches the
symbol owner` (`src/compiler/20.hir/hir_symbol_table_methods.spl`,
`bind_declaration_origin_v1`). `p2_add.spl` declares only 5 functions, so most
of the errors probably come from the import path
(`hir_lowering/_Items/module_import_registration.spl:397`). That path compares
`symbol.defining_module` against the module surface's
`declaration_authority.declaring_module`. The Stage 2 tree that produced the
errors is gone, so the real strings could not be recovered.

## Diagnostic (this change)
The error now prints the symbol name, the raw `defining_module` and its
canonical form, the raw `owner` and its canonical form, and `source_path`.
The extra text is built only on the error path. The next p2 build will
show which pair diverges.

## Ruled out
For declarations in the module itself, both sides come from
`self.module_filename`, and the seed interpreter canonicalised every spelling
of `p2_add.spl` to the same owner. Spellings tested: Windows absolute snapshot,
relative snapshot, POSIX absolute snapshot, `src/...`, and the dotted name.

## Open leads (probed with `hir_symbol_owner_module` in the seed interpreter)
1. **Alias spellings are passed through unchanged.** `hir_owner_name_is_canonical`
   returns any dotted name as it is, so an alias never meets the path-derived form:
   - `std.io.file` gives `lib.io.file`, but `.../src/lib/nogc_sync_mut/io/file.spl`
     gives `lib.nogc_sync_mut.io.file`.
   - `compiler.hir` gives `compiler.hir`, but `.../src/compiler/20.hir/__init__.spl`
     gives `compiler.hir.__init__`.

   This is the most likely cause on the import path. Not yet confirmed: which
   spelling each side carries at `module_import_registration.spl:397`.
2. **Latent separate defect: anchoring at the first `/src/`.** A snapshot root
   that itself contains `/src/` (for example
   `/home/dev/src/simple/build/scv/...`) canonicalises to
   `simple.build.scv...p2_add`, because `module_source_relative_path` cuts at
   the first `/src/`. The WSL host root is `/home/dev/simple`, which has no
   `/src/`, so this cannot be the p2 cause. The anchoring is deliberate and
   feeds native symbol names, so it is recorded here and not changed.
3. A difference that shows up only in the native build, such as
   `_module_logical_name_cache` dangling entries, would not reproduce in the
   interpreter.

## Next
Read the new error text from the next p2 Stage 2 run. Then write the failing
spec through `bind_declaration_origin_v1` with the real pair, plus a genuine
mismatch case that must still return `Err`, and fix it narrowly.

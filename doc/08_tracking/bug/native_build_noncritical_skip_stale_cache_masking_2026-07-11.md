# BUG: native-build "non-critical file skipped" + stale cache object silently links OLD code

**Status (2026-07-15):** source implemented fail-closed; focused regression
execution remains pending.
**Severity:** high (false build success; deployed kernels can run code that no longer matches any source revision)
**Component:** seed native-build pipeline — per-module compile skip + `.simple/native_cache` object reuse (`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`, dirty-set/cached-object path around line 573)
**Found:** 2026-07-11, SimpleOS RV64 DB gate investigation

## Symptom

When a source file fails codegen, native-build reports
`Warning: 1 non-critical file(s) failed to compile (skipped)` and continues.
If a previously cached object exists that still satisfies the module's
symbols at link time, the build completes "successfully" — silently shipping
the OLD object's code, compiled from a source revision that may no longer
exist in the working tree.

Observed sequence (RV64 SimpleOS, 2026-07-11):

1. `src/os/services/database/simple_db_service.spl` at HEAD fails LLVM
   verification (method-arity bug, see
   `stage4_seed_llvmlib_method_arity_2026-07-06.md`) — file "skipped".
2. Link nevertheless succeeds: a stale hashed object in
   `.simple/native_cache` (built weeks earlier from different source)
   provides `SimpleDbService.*` symbols.
3. `build/os/simpleos_riscv64.elf` boots and serves the OLD DB code; the QEMU
   gate fails with symptoms that do not correspond to the current source, and
   source-level fixes appear to "do nothing".
4. Only after `rm -rf .simple/native_cache` does the build fail honestly:
   `ld.lld: error: undefined symbol: os__services__database__simple_db_service__SimpleDbService.new`.

## Why this is dangerous

- Build exit code and "Build complete" output are indistinguishable from a
  genuinely current build.
- Debugging cost: runtime evidence contradicts the source being edited;
  every source-side fix is invisibly discarded.
- Combined with per-module content hashing, the stale object is only picked
  when the CURRENT source fails to compile — i.e. exactly when the mask is
  most misleading.

## Repro

1. Ensure `.simple/native_cache` contains an object for a module (any
   successful RV64 build).
2. Introduce (or, as on 2026-07-11, merely expose) a codegen failure in that
   module — e.g. non-`me` `fn` class methods called via `self.` on the seed
   LLVM backend.
3. Rebuild: warning is printed, link succeeds, binary contains the old code.
4. `rm -rf .simple/native_cache` and rebuild: link fails with undefined
   symbols — the honest result.

## Expected behavior

A module that fails to compile must fail the build (or at minimum must never
be substituted by a cache object whose source hash does not match current
source). "Non-critical" skipping should be opt-in and loudly reflected in the
exit status when the skipped module is in the entry closure.

## Resolution (2026-07-15)

Both the seed compatibility path and pure-Simple native driver now reject a
failed current-source compilation instead of accepting a stale cached object.
The focused stale-cache regression exists but was not executed in this
source-only audit.

## Related

- `doc/08_tracking/bug/stage4_seed_llvmlib_method_arity_2026-07-06.md` (the codegen failure that was masked)
- `doc/08_tracking/bug/codegen_stub_fallback_silent_exit0_2026-06-11.md` (sibling class: silent success on codegen fallback)
- `doc/08_tracking/bug/rv64_llvm_nested_len_arg_miscompile_2026-07-11.md` (runtime bug whose diagnosis this masking derailed)

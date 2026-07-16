# BUG: native-build "non-critical file skipped" + stale cache object silently links OLD code

**Status:** Resolved 2026-07-16 — fail-closed behavior verified by executed
regression on both the seed pipeline and the pure-Simple native driver (see
"Regression evidence" below).
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

## Regression evidence (2026-07-16)

Executed against a two-module fixture (`main.spl` importing `mod_a.spl`) with a
warm object cache holding a good object for `mod_a` from a previous successful
build, then breaking `mod_a` and rebuilding WITHOUT clearing the cache.

**Pure-Simple native driver** (`src/compiler/80.driver/driver.spl` +
`driver_aot_output.spl`, exercised live via interpreted `native-build --entry`):

- Prime: build OK, binary prints `v1-OLD-CODE`, `build_cache.sdn` + scoped
  object written.
- Break `mod_a` (`val x = nosuchfn(1)`), rebuild with the same `--cache-dir`:
  exit 1, `[ERROR] phase 3 FAILED` /
  `error: HIR lowering error in tmp_repro2.mod_a: unresolved name: nosuchfn`,
  NO output binary — the stale cached object is not substituted (the fatal
  allowlist in `_hir_lowering_error_is_fatal`, driver.spl, fails the build
  before the AOT cache phase; `BuildCache.has_cached_object`
  (driver_build/incremental.spl) additionally fingerprints cache entries
  against CURRENT source, so a failing changed source can never map to an old
  object).
- Restore source: build OK again, binary prints the current code.

**Seed pipeline** (`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`):

- No skip path remains: `grep -r "non-critical" src/` = 0 hits; any per-file
  failure returns `native-build aborted: N file(s) failed to compile`
  (mod.rs ~747) BEFORE object caching (step 6) and linking (step 7).
- Cache lookups key on the content hash of the CURRENT source
  (`object_cache_key`), and objects are stored only for `freshly_compiled`
  successes — a failing current source cannot hit a stale entry.
- Executed: warm cache + parse-broken module → exit 1
  (`Build failed: failed to parse ... during discovery`), no binary;
  warm cache + unresolved symbol under `SIMPLE_NO_STUB_FALLBACK=1` → exit 1
  (`Build failed: unresolved native symbols require stubs ...; preview=[nosuchfn]`),
  no binary, stale object not substituted.
- Good path: unchanged rebuild reports `1 compiled, 1 cached, 0 failed` and the
  binary reflects current source.

Residual note: `src/compiler_rust/driver/src/cli/native_build.rs:562` still has
a `Warning: {} files failed to compile` success branch, but it is unreachable —
`builder.build()` hard-errors when any file fails, so `result.failed` is always
0 on the Ok path. Seed is bootstrap-only tooling regardless.

## Related

- `doc/08_tracking/bug/stage4_seed_llvmlib_method_arity_2026-07-06.md` (the codegen failure that was masked)
- `doc/08_tracking/bug/codegen_stub_fallback_silent_exit0_2026-06-11.md` (sibling class: silent success on codegen fallback)
- `doc/08_tracking/bug/rv64_llvm_nested_len_arg_miscompile_2026-07-11.md` (runtime bug whose diagnosis this masking derailed)
- `doc/08_tracking/bug/native_build_entry_closure_skips_failed_modules_2026-07-13.md` (same class: skip-and-link on entry-closure dependency failures; the skip path it describes is likewise gone at this revision — failures abort before link — but its focused regression, a required module with a deterministic HIR error asserting no linker invocation, remains listed there)

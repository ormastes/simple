# rt_hash_text returns 0 under JIT/native — every cache source-hash check is vacuous

**Filed:** 2026-08-17
**Status:** OPEN
**Severity:** HIGH — silently consumes stale compiled artifacts
**Area:** compiler / cache consistency, runtime externs

## Summary

`rt_hash_text(s: text) -> i64` is declared `extern` in at least
`src/compiler/80.driver/cache/cache_validator.spl`,
`src/compiler/80.driver/watcher/smf_manifest.spl`,
`src/compiler/80.driver/watcher/watcher_daemon.spl` and
`src/compiler/80.driver/driver_aot_pipeline.spl`, and is the **only** hash
behind every source-freshness decision in the SHB/SMF cache.

It is implemented **only as an interpreter extern**:
`src/compiler_rust/compiler/src/interpreter_extern/conversion.rs:77`
(`pub fn rt_hash_text(args: &[Value]) -> Result<Value, CompileError>`).
There is no `rt_hash_text` in the Rust runtime crate source or the C runtime.
Under the JIT/native execution path it resolves to a zero stub and returns
**0 for every input**.

## Reproduction (measured 2026-08-17, `bin/simple` = Rust seed)

```
# scripts/check/_dbg_hash.spl
extern fn rt_hash_text(s: text) -> i64
fn main():
    print "h1={rt_hash_text("abc")} h2={rt_hash_text("fn main(): print 1")}"
```
`bin/simple run scripts/check/_dbg_hash.spl` prints `h1=0 h2=0`.

The same expression evaluated on a module that is *dropped to the interpreter*
(e.g. the identical file placed under `/tmp`, where the `compiler.*` import
fails to resolve and the JIT bails) prints real, distinct hashes
(`abc` -> `193485963`). So the divergence is exactly interpreter-vs-JIT.

## Why this is a correctness hole, not a perf issue

`cache_validator.validate_smf` (`src/compiler/80.driver/cache/cache_validator.spl:149`):

```
val current_src_hash = rt_hash_text(source)
if current_src_hash != smf_source_hash:
    return cache_check_result_stale(...)
```

With `rt_hash_text ≡ 0`, `current_src_hash` is 0 for *every* source. Any SMF
whose recorded header hash is also 0 (which is what the writers store, for the
same reason) compares EQUAL. The check does not merely weaken — it becomes
vacuously true, so **an arbitrarily stale .smf is reported FRESH and executed**.
The same applies to `validate_source_hash` and `validate_shb`.

The Level-3 options check cannot cover for it either: the sole caller,
`driver_api_interpret.try_load_smf_cached`, passes `compile_options_hash_zero()`,
and `validate_smf` skips the options comparison entirely when the supplied hash
is zero (`if not compile_options_hash_is_zero(options_hash)`).

## Mitigation already landed

`smf_manifest_entry_matches_source` (added 2026-08-17) treats a recorded
`source_hash == 0` as unknown provenance and **rejects** it, so the degenerate
case now fails closed at the interpreter's SMF cache lookup rather than
executing a stale artifact. That is containment for one consumer, not a fix.

## Real fix

Export a real `rt_hash_text` from the runtime (Rust `runtime/src/**`, and the C
runtime for the native lane) so the JIT/native path resolves the same function
the interpreter does, and make an unresolved runtime extern a hard error rather
than a zero stub — a silent zero-returning stub is fail-open by construction.

## Runnable detector

`bin/simple run scripts/check/check-smf-manifest-source-hash-verification.spl`
prints `NOTE: rt_hash_text is degenerate (returns 0) on this execution path`
whenever the defect is live.

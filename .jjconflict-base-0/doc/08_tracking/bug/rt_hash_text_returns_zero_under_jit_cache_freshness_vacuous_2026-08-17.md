# rt_hash_text returns 0 under JIT/native — every cache source-hash check is vacuous

**Filed:** 2026-08-17
**Status:** FIXED 2026-08-17 in source (JIT now returns the interpreter hash); needs a seed rebuild+redeploy to take effect for `bin/simple` users
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

## Root cause — NOT a missing runtime export

The row's premise ("there is no `rt_hash_text` in the Rust runtime crate source
or the C runtime") is **wrong as measured in this checkout**: it exists in both,
`src/compiler_rust/runtime/src/value/collections.rs:4452`
(`pub extern "C" fn rt_hash_text(string: RuntimeValue) -> i64`, djb2, the same
algorithm and the same values as the interpreter extern) and
`src/runtime/runtime_native.c:7791`, and it is in the JIT symbol table
(`src/compiler_rust/common/src/runtime_symbols.rs:587`).

The zero came from an **inline codegen fast path**, not from symbol resolution.
The decisive experiment: `rt_str_hash` is a thin alias of the very same runtime
function, and in ONE program under `SIMPLE_EXECUTION_MODE=jit`

    A={rt_hash_text(a)} B={rt_str_hash(a)}   ->   A=0 B=193485963

Same engine, same string, same underlying implementation — so the runtime symbol
was fine and only the name `rt_hash_text` was being intercepted.
`src/compiler_rust/compiler/src/codegen/instr/calls.rs` intercepted it with
`compile_inline_hash_text`, which re-implemented the string heap layout in
Cranelift IR (`tag == 1`, `kind == 'STRI'`, len at +8, data at +16) and branched
to a literal **0** on every assumption failure. Those assumptions did not hold,
so it emitted 0 for all inputs. This is the same sentinel-that-is-not-a-sentinel
family as the rest of the fail-open cluster: an unmet precondition returned a
plausible VALUE instead of an error.

## Fix landed

The inline path is deleted (call site + the ~150-line
`compile_inline_hash_text`), so `rt_hash_text` always calls the real runtime
symbol. `cargo check --release -p simple-compiler` clean; `cargo build --release
--bin simple` exit 0.

## Verification (A/B, one tree, two binaries)

Probe: `extern fn rt_hash_text(s: text) -> i64` printing `rt_hash_text("abc")`
and `rt_hash_text("xyz")`.

| binary | interpreter | jit |
|---|---|---|
| `bin/simple` (deployed seed, 12:58 2026-08-17, pre-fix) | `h1=193485963 h2=193511792` | **`h1=0 h2=0`** |
| `/mnt/data/cargo-hashfix/release/simple` (this fix) | `h1=193485963 h2=193511792` | **`h1=193485963 h2=193511792`** |

The row's own runnable detector agrees, and is non-vacuous — it still reports the
defect on the old binary:

    ./bin/simple run scripts/check/check-smf-manifest-source-hash-verification.spl
    NOTE: rt_hash_text is degenerate (returns 0) on this execution path;
    PASS — 4 case(s) checked, 0 failed                                   (exit 0)

    /mnt/data/cargo-hashfix/release/simple run scripts/check/check-smf-manifest-source-hash-verification.spl
    PASS — 6 case(s) checked, 0 failed                                   (exit 0)

(no `degenerate` NOTE, and 6 cases instead of 4 — the two extra cases are the
ones the detector can only exercise when the hash is real).

**Not done:** the fixed binary was NOT deployed over `bin/simple` — other lanes
are using that symlink. Until a seed rebuild lands, `bin/simple` still returns 0
under JIT and the `smf_manifest_entry_matches_source` containment remains the
thing standing between a stale `.smf` and execution. The row's second ask —
"make an unresolved runtime extern a hard error rather than a zero stub" — is a
separate, wider change and is NOT addressed here.

## 2026-08-17 20:1x — RESOLVED on the DEPLOYED seed

Binary: /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple (bin/simple), md5 669150b61f2f20401a6a895ae54e9fee, 59550432 bytes, mtime 2026-08-17 20:10:45 — the REDEPLOYED seed carrying this session's fixes.

```
$ env SIMPLE_EXECUTION_MODE=jit bin/simple run hash.spl
h1=193485963 h2=193511792
$ env SIMPLE_EXECUTION_MODE=interpreter bin/simple run hash.spl
h1=193485963 h2=193511792
$ bin/simple run scripts/check/check-smf-manifest-source-hash-verification.spl
PASS — 6 case(s) checked, 0 failed          (rc=0)
```

JIT hashes are nonzero and identical to the interpreter; the detector reports 6
cases (not the degenerate 4) with no `degenerate` NOTE. Matches the
isolated-build result. **Status: RESOLVED.**

# `text` has no `.to_bytes()` method, only a free `text_to_bytes()`

- **Filed:** 2026-09-05
- **Lane:** `src/compiler_rust/target/debug/simple` (debug Rust seed, built from current source)
- **Severity:** stdlib surface gap — the method form every caller reaches for is missing

## Symptom

```
$ cat repro.spl
fn main():
    val b = "ok".to_bytes()
    print(b.len())

$ src/compiler_rust/target/debug/simple run repro.spl
Runtime error: Function 'str.to_bytes' not found
Runtime error: unresolved symbol -- this is a code-generation dispatch gap, not a program error. Refusing to substitute a placeholder value (it would render as the text 'error' and silently corrupt output).
```

## What exists instead

`src/lib/common/string_core.spl:428` declares the conversion as a free
function:

```
pub fn text_to_bytes(s: text) -> [u8]        # wraps extern rt_text_to_bytes
```

and `:431` the inverse, `bytes_to_text(bytes: [u8]) -> text`. The runtime
extern `rt_text_to_bytes` is real and backed. Only the *method* spelling is
absent, so the capability is present and merely unreachable in the form
callers write.

The asymmetry is visible in the same file: other `text` operations are
reachable as methods, and `[u8]`-producing types elsewhere in the tree do
expose `me fn to_bytes() -> [u8]` (`src/lib/common/binary_io.spl:537,675`), so
`.to_bytes()` is the established spelling everywhere except on `text` itself.

## Impact

`test/03_system/plan_acceptance/cuda_host_validation_spec.spl`
(REQ-CUDA-VALIDATION-03) writes `"ok".to_bytes()` to build a PTX payload. The
scenario fails on this gap before it ever reaches the assertion it exists to
make, so the checkbox it pins cannot be evaluated at all — the failure is the
missing method, not the JIT-load contract under test.

The spec is not the place to fix this: rewriting it to `text_to_bytes("ok")`
would work around a real stdlib gap in the one file that documents it.

## Expected

`text` exposes `to_bytes() -> [u8]`, dispatching to the same
`rt_text_to_bytes` extern `text_to_bytes` already uses, so both spellings name
one implementation.

## Note on scope

This is a builtin-type method surface, so the fix is not purely a `src/lib`
edit — `str` method dispatch is resolved in the seed. That is why this is
filed rather than fixed in the interface lane that found it.

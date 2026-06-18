# BUG: calling a missing/unknown extern that returns a pointer type SIGSEGVs

- **ID:** `interp_missing_pointer_extern_nil_deref_sigsegv`
- **Severity:** P2 (crash, but only on calling an undefined extern — a program bug;
  still: a clean error is required, never a SIGSEGV)
- **Found:** 2026-06-18, while scoping rt-encapsulation Stage 2 wrappers.

## Symptom
A call to an extern function that is **not registered** in the interpreter
(`call_extern_function_with_values` → E1002 "unknown extern function") returns
`RuntimeValue::NIL` from the dispatch error arm
(`interpreter_sffi.rs:735`). This is intentional leniency (see the comment at
`interpreter_sffi.rs:705-707`: torch-less builds expect some `rt_torch_*` missing
and handled). The crash happens when the caller then **uses that NIL as a
pointer-typed value** (array/`[u8]`/`text`): the value-returning case is safe, the
pointer-returning case crashes.

## Minimal repro (isolated 2026-06-18)
```simple
# Test B — missing VALUE-returning extern: CLEAN (prints error, returns 0, exit 0)
extern fn rt_nonexistent_val_xyz() -> i64
fn main():
    val x = rt_nonexistent_val_xyz()   # E1002 logged, x = 0
    print(x)                            # prints 0, no crash

# Test C — missing POINTER-returning extern: SIGSEGV
extern fn rt_nonexistent_arr_xyz() -> [text]
fn main():
    val x = rt_nonexistent_arr_xyz()   # E1002 logged, x = NIL
    print(x.len())                      # <-- SIGSEGV (core dump)
```
Test B errors cleanly; Test C errors then cores. Same for `-> text` / `-> [u8]`.

## Root cause (traced, not the obvious layer)
- Dispatch returns `RuntimeValue::NIL` on a not-found extern (`interpreter_sffi.rs:733-736`).
- The guarded runtime op `rt_array_len` (`runtime/src/value/collections.rs:420`) is
  **NIL-safe**: `as_typed_ptr!` → `get_typed_ptr` returns `None` for NIL → returns the
  fallback (`-1`). So `rt_array_len(NIL)` does NOT crash.
- Therefore the crash is the **caller path dereferencing the NIL return as a pointer
  before reaching the guarded op** — i.e. interpreter/JIT lowering of `.len()`
  (and indexing) on an extern result inlines a raw pointer load that assumes a valid
  heap object, bypassing `rt_array_len`'s guard. That is the fix site.

## Fix candidates
1. Make a not-found extern whose declared return is a pointer type return a *typed
   empty* (`rt_array_new()` empty array / empty string) instead of bare `NIL`, so the
   caller's pointer load is valid. (Dispatch doesn't currently see the return type —
   would need to thread it through, OR)
2. NIL-guard the interpreter/JIT lowering of `.len()` / index / field access so a NIL
   receiver routes through the guarded runtime op (returns -1/NIL) instead of a raw
   deref. Broadest protection (covers any NIL-as-pointer, not just missing externs).
3. Make a not-found extern a hard, clean halt — REJECTED: breaks the intentional
   leniency for optional native features (torch-less builds).

Recommendation: (2) — null-safe the pointer-deref lowering — is the correct,
general fix. It is a codegen/interpreter change, not a one-liner; do it as a
focused change with its own verification (re-run Test C → clean error).

## NOT a separate bug
`rt_file_list_dir` is registered (`interpreter_extern/mod.rs:1059` → `file_io::rt_dir_list`,
the same impl as the working `rt_dir_list`/`dir_list`). It only appeared to
"core-dump" during Stage-2 scoping because the **deployed binary was stale** (lacked
that registration) AND it returns `[text]` — so it hit exactly this bug. After a
rebuild it resolves normally. (Corrects the misstatement in the Stage-2 plan /
revert commit `4c7986171bb`.)

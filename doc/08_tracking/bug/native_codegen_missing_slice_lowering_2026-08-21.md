# Native codegen has no lowering for `Expr::Slice` — functions using `a[i:j]` silently emit nothing

- Date: 2026-08-21
- Area: compiler / native codegen (AOT `--native`)
- Severity: medium-high — it is the sole remaining blocker on the enterprise
  suite's AC-5/AC-6 native-ACID stage 2, and it blocks the standalone-native
  path for any code reaching `src/lib/common/string_core.spl`, i.e. most string
  handling in the language.
- Status: OPEN, feature request. Filed rather than worked around, per CLAUDE.md
  ("When a short, safe grammar or compact expression form fails … fix it or
  record a concrete bug/feature request instead of silently normalizing the
  workaround").

## Symptom

`compiler_rust/compiler/src/compilability.rs:529` marks any function containing
`Expr::Slice` as `FallbackReason::CollectionOps`, so AOT `--native` refuses it:

```
error: semantic: cannot compile to standalone native binary:
13 function(s) contain constructs that require the interpreter:
  - str_char_at, str_ends_with, str_index_of, str_last_index_of,
    str_replace_all, str_reverse, str_safe_slice, str_slice, str_starts_with,
    str_to_lower, str_to_upper, str_trim_left, str_trim_right   [all CollectionOps]
```

All 13 live in `src/lib/common/string_core.spl` (mirrored in
`src/lib/nogc_sync_mut/src/text_utils.spl`).

## The rejection is load-bearing — removing it is NOT the fix

Measured 2026-08-21 in a throwaway worktree, rejection commented out, seed
rebuilt. A three-line program is enough:

```simple
fn main():
    val t = "hello world"
    print("A:" + t[0:5])
    print("B:" + t[6:11])
    print("H:" + t[3:3])
```

- Interpreter (oracle): `A:hello  B:world  H:` — correct, including the empty slice.
- Native, rejection removed: **`ld: symbol(s) not found for architecture arm64`,
  `"_main"` referenced from `_main_shim.o`.**

The semantic stage accepts the function and codegen emits **nothing** for it, so
the entry symbol never appears. That is the actual gap: **there is no native
lowering for slice**, and the `:529` rejection is what turns a missing feature
into an honest, actionable diagnostic instead of an undefined-`_main` mystery.

This corrects an earlier reading (lane W12-C's note, and a 2026-08-21 entry in
`store_open_acid_gate_unrunnable_on_macos_aarch64_2026-08-17.md`) that treated
`:529` as bookkeeping around a missing `rt_slice` allowlist entry, with
`rt_slice` "already threaded into standalone symbol emission at four sites". The
allowlist is not the blocker; emission is.

## Why the obvious workaround is also wrong

The 13 helpers could be rewritten with char-index loops instead of `[i:j]` —
the pattern this repo already uses for guest/freestanding code (`.claude/skills/spipe.md`:
"native array `[s:e]` slice + `.join()` is unreliable in guest-run code; use
index loops"). **Do not do this here.** Those helpers are core stdlib string
primitives used across the whole language, so the change would carry a
correctness and performance risk far wider than the gap it hides, and it is
precisely the "silently normalizing the workaround" that CLAUDE.md forbids. The
guest-code precedent applies to code that must run without a full runtime; it is
not a licence to rewrite `string_core` around a compiler limitation.

## Reproduction

```sh
# 1. Baseline: the honest refusal
simple compile <file-with-a-slice>.spl --native -o /tmp/out
#    -> "N function(s) contain constructs that require the interpreter: … [CollectionOps]"

# 2. With compilability.rs:529's add_reason(...) commented out and the seed rebuilt
simple compile slice_probe.spl --native -o /tmp/out
#    -> ld: symbol(s) not found for architecture arm64 ("_main")
```

Measured with text slices (`t[a:b]`, including an empty slice). Array slices and
the `step` form (`a[0:6:2]`) were not separately measured, because the baseline
rejects them before codegen; expect the same gap.

## Fix

Implement MIR lowering + backend emission for `Expr::Slice` on text and array
receivers, covering start/end/step and the empty-slice case, then remove the
`:529` rejection. Sequencing note from W12-C stands: the sibling `ArrayRepeat`
rejection at `:879` additionally needs `rt_array_repeat` wired into the
standalone symbol allowlist (it appears in exactly one file,
`codegen/runtime_sffi.rs:267`), so relaxing that one today would link-fail.

**Acceptance for the fix must call a slice at runtime and compare against the
interpreter oracle.** Compiling is not evidence: see below.

## Related — a vacuous-pass trap this uncovered

With the rejection removed, `scripts/check/check-store-open-acid.shs` reports
`PASS — 9 stage(s) checked … native store_backend_acid=true`. That green is
worthless: the 13 helpers are called **zero** times by
`test/fixture/enterprise_store/store_native_acid_probe.spl`, enter the compile
only through `use std.nogc_sync_mut.enterprise_store.store`, and are
dead-stripped. Stage 2 would stay green through a completely broken `str_*`
implementation. Gate hardening (call a slice-using store helper and assert its
result) is filed in
`doc/08_tracking/bug/store_open_acid_gate_unrunnable_on_macos_aarch64_2026-08-17.md`.

## Impact on the enterprise lane

AC-5/AC-6's ACID *property* is already proven natively — real sqlite, real
`ROLLBACK`, `acidD=true`, stage 1 of the same gate, and it needs no slice. What
this bug blocks is stage 2, "the store module itself compiles standalone-native".
That is a compiler-completeness property, not a durability one.

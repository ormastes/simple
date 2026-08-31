# `text + char_at(i)` yields EMPTY on the Stage-2 native lane

- **Filed:** 2026-08-31
- **Status:** OPEN — mechanism measured, one fix attempted and REVERTED (made it worse)
- **Blocks:** Stage-2 admission arm 2 (`stage2 positional Stage-3 route returned unexpected output:`), therefore Stages 3/4/5
- **Platform:** aarch64-apple-darwin. **NOT shown to be macOS-specific.**
- **Upstream:** no existing fix — `main@origin` log and all PRs checked for
  char_at/tagged/concat work; nothing matches.

## Symptom

Every char-accumulation loop silently produces an empty string, so
`module_logical_name_from_path` returns `""` and the Stage-2 gate reports
`returned unexpected output:` (empty).

## Minimal repro, streams separated

```
val s: text = "abc"
print(s.char_code_at(0).to_text())   # [code]97   CORRECT
print(s.char_at(0))                  # [at]a      CORRECT
var p: text = ""
p = p + s.char_at(1)
print(p)                             # [cat]      EMPTY  <-- defect
```

stderr additionally carries, once:

```
[simple-runtime][error] rejected invalid array handle before dereference;
probable compiler/FFI ABI mismatch (value_bits=0x0000000100a25420)
```

`value_bits` is a raw pointer. **Separate stdout from stderr when reading this** —
interleaved, the error appears before the first marker and looks like an early
abort rather than a mid-loop rejection.

## Mechanism

`char_at` (`_MirLoweringExpr/method_calls_literals.spl:2282`) returns the result
of `spl_str_slice` directly, typed `MirType Opaque("str")` — a RAW `char*`, not a
tagged handle. `print` accepts raw, so the standalone call looks correct; the
concat path consumes it as tagged, and the runtime's handle guard rejects it and
yields empty. The guard is doing its job: it reported an ABI mismatch instead of
dereferencing a raw pointer.

## ATTEMPTED FIX — REVERTED, do not repeat as-is

Wrapping the result in `ensure_tagged_str` (the in-tree helper that does a
runtime tagged-or-raw check via `rt_interp_cstr` before re-tagging, and is
documented as safe for both representations) **made it worse**:

| | before | after |
|---|---|---|
| `print(s.char_at(0))` | `a` | `4372273249` (handle rendered as int) |
| `p + s.char_at(1)` | empty | **still empty** |
| runtime errors | 1 | 0 |

It broke the previously-correct standalone case and did not fix concat. The
`errs=0` is a REGRESSION, not progress: the guard was silenced while the value
stayed wrong — strictly worse than a loud rejection. Reverted.

What that rules out: the defect is not simply "the result lacks a tag". Tagging
it satisfies the guard yet still produces an empty concat, so the concat path
itself mishandles this value, or `print` and `+` disagree about the
representation in a way a single re-tag cannot reconcile.

## Refuted en route (measured, do not re-propose)

- **`text.replace` miscompiles.** The same source file carries a comment claiming
  Stage-2 native turns a path into `""` via `replace`. Measured: `"a/b/c".replace("/", ".")`
  -> `a.b.c`, correct. That comment is stale for this case and would have sent a
  fix to the wrong function.
- **Array push/len/join broken.** Measured: `[len]2[join]a/b`, all correct. This
  also confirms the aggregate and cross-file trait-override fixes landed earlier
  in this branch work at RUNTIME, not merely in the emitted IR.
- **`starts_with`/`substring`/`ends_with`.** All correct in the bisect
  (`[sw]app/cli/bootstrap_main.spl`, `[ew]app/cli/bootstrap_main`).

## Next

Compare how a KNOWN-WORKING text-returning builtin (e.g. `substring`, proven
correct above) represents its result against `char_at`, and make `char_at` match
that representation rather than adding a tag on top. `substring` flows through
concat correctly, so its representation is the reference.

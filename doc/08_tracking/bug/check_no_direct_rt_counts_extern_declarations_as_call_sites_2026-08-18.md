# `check-no-direct-rt.shs` counts `extern fn rt_*` DECLARATIONS as "call sites"

- **Status:** OPEN
- **Date:** 2026-08-18
- **Area:** `scripts/check/check-no-direct-rt.shs` (the `RT_RE` matcher)
- **Severity:** Medium — the gate's headline number is inflated, and the
  inflation is concentrated exactly in the FFI-binding files the allowlist
  decisions are made about.
- **Found while:** classifying provider candidates for the rt_ boundary
  (binary_runtime_hardening goal 1).

## Summary

The gate matches

```sh
RT_RE='^[^#]*\brt_[a-z0-9_]*\('
```

and reports the result as *"direct rt_* call site(s)"* in its verdict and its
fix-it guidance. But that regex also matches a **declaration**:

```
extern fn rt_vulkan_create_instance(app_name: text) -> i64
```

which is not a call site. It is a symbol declaration, and one that pure-Simple
FFI binding code cannot avoid writing.

## Measured (2026-08-18)

| file | `RT_RE` matches | of which `extern fn rt_` declarations |
|---|---|---|
| `src/lib/nogc_sync_mut/io/vulkan_sffi.spl` | 111 | **74** (67%) |
| `src/lib/nogc_sync_mut/io/metal_sffi.spl` | 111 | 43 (39%) |

So two thirds of the "call sites" in the single largest Vulkan binding file
are declarations.

## Why it matters

1. **The verdict is mislabeled.** `FAIL — ... N forbidden direct rt_* call
   site(s)` overstates actual call sites, and the number is what the phase
   A/B/C promotion in
   `doc/03_plan/infra/binary_runtime_hardening/plan.md` ratchets on.
2. **It biases allowlist decisions.** A binding file looks like a much bigger
   offender than it is, which makes allowlisting it look like a much bigger
   "win" than it is. The provider classification recorded in
   `doc/08_tracking/rt_boundary/provider_classification_2026-08-18.md` notes
   the same distortion.
3. **It conflates two different things the design separates.** Frozen design
   §12 distinguishes the *public semantic API* (must not expose an `rt_` name)
   from the *provider boundary* (may declare and call the primitive). A
   declaration and a call want different treatment; today they are one number.

## Note on the baseline

Because this affects the count, it also affects the recorded baseline. Do not
"fix" the regex and re-record the baseline in the same change without stating
both numbers — otherwise the drop reads as migration progress when no call
site was actually removed.

## Suggested fix

Emit declarations and calls as **separate** measured counts, matching the
design's structured-count requirement (`direct_total = allowed_provider +
generated_boundary + test_oracle + forbidden_product + unclassified` — none of
which exist yet either; today the script only produces `allowed_provider` and
`forbidden_product`). Minimum viable version: exclude lines matching
`^\s*extern fn rt_` from the call-site count and report them on their own line,
e.g.

```
  forbidden_product: <n>
  extern_declarations: <m>
```

Keep both in the verdict so neither can be silently dropped.

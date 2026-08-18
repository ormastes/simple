# `check-no-direct-rt.shs` counts `extern fn rt_*` DECLARATIONS as "call sites"

- **Status:** RESOLVED (scanner fixed 2026-08-18); baseline re-record still OPEN — see Resolution
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

## Resolution (2026-08-18) — FIXED in the scanner, baseline NOT re-recorded

`scripts/check/check-no-direct-rt.shs` now subtracts declaration lines
(`DECL_RE='^[[:space:]]*extern[[:space:]]+fn[[:space:]]+rt_[a-z0-9_]*\('`) from
the call-site count and reports them as their own structured line. Every
pre-existing structured count line is retained, plus two new ones:

```
  forbidden_product: <n>
  extern_declarations: <m>
  match_total_incl_declarations: <direct_total + m>
```

`extern_decls=<m>` is also carried in every PASS/FAIL verdict line so the
number cannot be silently dropped. FAIL-over-baseline (exit 1), ERROR on
scanned==0 (exit 2), `--critical`, `--selftest-only`, `--update-baseline`
(a default run still never writes the baseline), the verdict-is-last-stdout-line
contract, and the fix-it guidance printed before the verdict are all unchanged.
The fatal selftest grew from 5 to 8 fixtures: an `extern fn rt_x(...)` line must
count as a declaration and NOT as forbidden; a real `y = rt_x(a)` must still
count as forbidden and not as a declaration; a file containing both must split
2 declarations / 1 call.

### Both numbers, measured on the same tree (2026-08-18)

| definition | scanned files | direct_total | allowed_provider | forbidden_product | extern_declarations |
|---|---|---|---|---|---|
| OLD (declarations counted as call sites) | 14828 | 21191 | 2625 | **18566** | not measured |
| NEW (declarations excluded) | 14828 | 13675 | 1663 | **12012** | **7516** |

`13675 + 7516 = 21191` — the new split reconciles exactly with the old total, so
nothing was lost, only reclassified.

**The 18566 -> 12012 drop is a MEASUREMENT-DEFINITION change, not migration
progress. Zero call sites were removed by this change.** (The `allowed_provider`
side falls 2625 -> 1663 for the same reason: allowlisted provider files also
declare their externs.)

### Baseline decision: left untouched, deliberately

`scripts/check/no_direct_rt_baseline.txt` still reads **18788**, recorded under
the OLD definition, and a default run continues to leave it unwritten
(`git status --porcelain` on it is empty after a default run). It is left for
the owner of the phase A/B/C ratchet in
`doc/03_plan/infra/binary_runtime_hardening/plan.md` to re-record, because
re-recording is what makes the new floor binding and that is a plan decision,
not a scanner decision.

**It should become 12012** (the new-definition measurement on this tree), via
`sh scripts/check/check-no-direct-rt.shs --update-baseline`, and whoever does it
must cite this note so the 6776 delta is never read as work done. Until then the
gate is loose by ~6776 against the new definition — it will PASS on real
regressions of up to that size, so re-record promptly. Note also that the
allowlist is being edited in parallel, which moves `allowed_provider` /
`forbidden_product` independently of this fix; re-measure immediately before
recording.

Status: **RESOLVED (scanner)** / baseline re-record OPEN.

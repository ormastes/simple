# The "148 stale specs" cluster is NOT stale — the APIs exist, and deleting these specs would have destroyed live coverage

Date: 2026-08-23
Lane: spectriage-1
Status: OPEN — reclassification recorded; no spec deleted, no spec weakened
Engine: Rust seed `bin/release/x86_64-unknown-linux-gnu/simple`, 60650360 bytes, 2026-08-23 04:47

## The claim being refuted

The triage brief handed down to this lane (and the phase-1 sweep clusters
`B-spec-api-drift` 72 rows + `B-spec-source-text-drift` 76 rows = 148) states:

> 148 stale specs ... it tests an API that no longer exists (`lower_module`,
> `TreeSitter`, `ptx_mir_kind_to_primitive` are absent from `src/` entirely;
> these fail against ANY compiler) ... if the feature is genuinely gone, remove
> the spec.

**Two of the three named symbols are not absent, and neither is any other symbol
sampled from the cluster.** Measured with `/usr/bin/grep -rl <sym> src/ | wc -l`
(the wrapped ugrep honours .gitignore, so `/usr/bin/grep` is used deliberately):

| symbol | files in `src/` | brief's claim | verdict |
|---|---|---|---|
| `lower_module` | **65** | absent | FALSE |
| `TreeSitter` | **63** | absent | FALSE |
| `ptx_mir_kind_to_primitive` | 0 | absent | TRUE (2 specs, not 148) |
| `MirLowering` | **54** | — | present |
| `value_of` | **38** | — | present |
| `translate_terminator` | **7** | — | present |
| `header_target` | **1** | — | present |

Had this lane executed its brief as written, it would have deleted on the order
of 148 specs covering APIs that are alive and shipping. That is the destructive
outcome the "PASSING or explicitly not-yet-implemented" policy exists to prevent,
arriving through the one category that authorises deletion.

## What is actually wrong (root cause, one worked case)

`test/01_unit/compiler/backend/cuda_source_global_pointer_abi_spec.spl`
fails with `semantic: variable `MirLowering` not found`. The spec does:

    use compiler.mir.mir.*            # line 10 — glob
    var mir_lowering = MirLowering.new(hir.symbols)   # lines 27, 53, 68

and the type is defined at `src/compiler/50.mir/mir_lowering_types.spl:18`:

    struct MirLowering:

**`mir_lowering_types.spl` carries no `export` line for it at all**, and
`src/compiler/50.mir/mir.spl` names `MirLowering` only inside a comment
(`mir.spl:8`, "Struct definitions (MirLowering, MirError)") — it never re-exports
it. So `use compiler.mir.mir.*` cannot surface the name, and the resolver is
telling the exact truth: no *variable* `MirLowering` is in scope.

This is **an unexported/mis-re-exported symbol reachable only by the wrong import
path** — a module-surface defect — not a deleted feature. The correct dispositions
are "fix the export / fix the spec's import path", never "remove the spec".

Note the failure MESSAGE is what misled the classifier: `variable X not found` and
`method X not found on type nil` read like a vanished API, but are equally produced
by a name that exists and is merely not exported into the path the spec imports.
A classifier keyed on the message text cannot separate the two; only a grep of
`src/` can, and that grep is what the 148-row cluster never had applied to it.

## Measured over the WHOLE cluster (not a sample)

Every backtick-quoted identifier was extracted from the `B-spec-api-drift`
failure messages (54 distinct symbols) and checked for presence in `src/` in a
single combined scan:

    TOTAL=54  PRESENT=48  ABSENT=6      -> 11% genuinely absent, 89% alive

The 6 genuinely absent symbols, in full — these are the ONLY stale-API
candidates the cluster actually contains, and each still needs its own recorded
reason before anything is removed:

    ffi_in_verified_error
    first_unemitted_call_destination
    is_model_complete
    ptx_mir_kind_to_primitive
    resolve_flat_methods
    simpleos_forbidden_allocator_symbols_from_names

So the defensible figure is **~6 stale symbols, not 148 stale specs** — and the
other 48 name live code that the specs simply cannot reach.

## Impact on the cluster

`B-spec-api-drift` (72) and `B-spec-source-text-drift` (76) must be re-triaged
against symbol presence in `src/` before any of them is touched. On the sample
taken here the stale rate is **1 symbol of 7** — and that one accounts for 2 spec
files, not 148. The cluster label "stale" is not supported by evidence for the
overwhelming majority of its members.

`B-spec-source-text-drift` is a further distinct shape not addressed above: those
rows assert on SOURCE TEXT of product files (`expected # Lightweight entrypoint
for `simple native-build`.`). Those fail when the product file is legitimately
edited. They are neither stale APIs nor product defects — they are over-tight
source-text pins, and deleting them is also wrong.

## Twin verdict (cross-implementation rule)

Not applicable in the divergence sense, and stated rather than skipped: this is a
**module-surface/export** defect in Simple source (`src/compiler/50.mir/**`), not
engine behaviour. Both engines resolve `use ... .*` against the same `.spl`
export lines, so an unexported struct is invisible to both; there is no
"passes on one engine" side. Verified the symbol is absent from the seed's own
surface too — the Rust seed does not define a `MirLowering` export that could
mask the gap.

## What this lane did NOT do, deliberately

* Deleted no spec. Removed no assertion. Weakened no matcher.
* Marked nothing `@tag:in-development` on the strength of the "stale" label —
  a live API failing to resolve is a product/module-surface defect (category 1),
  not a not-yet-implemented feature (category 2), and tagging it would have
  converted a real defect into sanctioned debt.

## Follow-up

Re-run the cluster with a symbol-presence pre-filter: for each row, extract the
unresolved name from the message and record `grep -rl <name> src/ | wc -l`.
Rows with count > 0 are export/import defects; only rows with count 0 are
candidates for the stale category, and each still needs its own reason recorded.

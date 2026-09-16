# jit-module-drop fence: 43% NOT MEASURED, and its own gap breakdown was mislabelled

- **Filed:** 2026-08-18
- **Fence:** `scripts/check/check-no-jit-module-drop.shs`
- **Oracle used for every number here:**
  `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
  (`59546088/1787039619`), `timeout=120s`, worktree `/mnt/data/worktrees/g-jit-drop`
  at `ce396605fef`.

## 1. The reported FAIL is STALE — the tree is green

Reported (older tree):

```
FAIL — 415 selected, 239 MEASURED (57%), 176 NOT MEASURED; 1 with a paren-less
accessor whole-module de-JIT (122 compiled clean, 116 lowered-clean).
```

Re-run on pristine `origin/main` (`ce396605fef`), full output:

```
selftest: OK (known-bad -> DROP, known-good -> CLEAN, non-standalone -> LOWERED_CLEAN,
non-standalone+accessor -> DROP, semantic-failure -> UNMEASURABLE; 5 fixtures, both directions)
scanning 419 file(s) — roots:src/lib src/app src/os src/compiler [--candidates: textual
superset filter, 13681 file(s) in roster before filtering]
NOT MEASURED: 180 of 419 selected file(s) never reached the oracle.
      breakdown: undefined-identifier=114 parse=2 lint=18 smf-emission=11 timeout=0 silent=0 other=35   [pre-fix labelling; see 3]
PASS — 239 of 419 selected module(s) MEASURED (57%), 0 paren-less accessor de-JIT drops;
180 NOT MEASURED and NOT covered by this verdict (126 compiled clean, 113 lowered-clean),
selftest fired in both directions. oracle=...(59546088/1787039619) timeout=120s
```

exit 0. **Zero drops.** The single drop was the six-site `.length` family fixed
by `4bc0aa626e8` ("fix(lang): 6 paren-less `.length` accessors made 3 modules
uncompilable"), fenced by
`test/01_unit/compiler/paren_less_length_accessor_guard_spec.spl`. The fence is
not blocking pushes on this tree; a caller seeing the FAIL above is on a tree
predating that commit.

Root cause of the de-JIT class itself is unchanged and already recorded:
`hir/lower/expr/access.rs:424` cannot infer a field type for `Array`/`String`/
`Dict` pseudo-fields, raising `LowerError::Unsupported`; the `run` lane used to
swallow it and drop the whole module to the tree-walk interpreter.
`SIMPLE_JIT_STRICT=1` does **not** harden this path (the message is not tagged);
`exec_core.rs:is_parenless_container_accessor` now escalates this class to a
hard error unconditionally. See
`doc/08_tracking/bug/paren_less_accessor_whole_module_de_jit_2026-08-08.md`.

## 2. The 180 NOT MEASURED, by cause

**It is not the timeout.** `timeout=0` and `silent=0`: not one of the 419 files
hit the 120s budget on this box. Raising the budget would measure zero
additional files. This is neither guard tuning nor compiler slowness.

Every unmeasured file failed `simple compile` *before* HIR lowering of its
bodies, for a reason unrelated to the accessor class. Corrected buckets (see §3
— the `other=35` above was a labelling artefact):

Measured after the §3 fix (same oracle, same 419 selected, same verdict —
`other` collapsed from 35 to 1):

| cause | n | what it means |
|---|---:|---|
| undefined-identifier | 121 | single-file compile has no package context: `Undefined("undefined identifier: Port" / "CapabilitySet" / "process_run" ...)` |
| lint | 18 | lint refused before the compiler ran |
| smf-emission | 17 | `SMF emission failed` after lowering, not the standalone-SMF fallback case |
| import | 9 | `HIR lowering: cannot resolve import` |
| type-error | 7 | `struct DirEntry has no field name`, `MIR lowering: Unsupported` |
| codegen | 5 | `Failed to parse object into relocation-aware SMF` |
| parse | 2 | source does not parse for this compiler |
| timeout | **0** | — |
| silent | **0** | — |
| other | 1 | genuinely unattributed |

So ~72% of the gap is one thing: **the probe compiles one file at a time, and
these modules cannot resolve their siblings that way.** Closing it needs a
package-aware probe (compile the owning package, attribute the diagnostic back
to the file), not a bigger timeout and not a smaller corpus. Filed as the
follow-up below; deliberately NOT worked around by shrinking the roster.

## 3. Defect fixed here: the fence bucketed a TRUNCATED message

`reason="$(grep -m1 -E '^error' "$log" | cut -c1-160)"` truncated the first
error line and the `case` then matched the truncated text. Repo paths are long
and the compiler prints the path twice, so the distinguishing keyword was
routinely past the cut and the file fell into the catch-all `other`.

Measured on run `build/check/jit-module-drop/run-379301-1787045145`: **33 of 35
`other` entries were truncated mid-message**, and among them 4 were
`SMF emission failed` — an *existing* bucket the truncation was hiding — plus 5
`cannot resolve import`, 5 `has no field`, 6 `Failed to parse object`.

Fix: match on the untruncated line, truncate only for the recorded reason; add
`import`, `type-error`, `codegen` buckets. **No file moves into the MEASURED
count and no verdict can change** — this relabels only the already-unmeasured
remainder. Specs:

- `test/01_unit/scripts/jit_drop_guard_bucket_truncation_spec.spl` (reproducing)
- `test/01_unit/scripts/truncate_before_classify_defect_class_spec.spl`
  (defect CLASS: truncate-then-classify vs classify-then-truncate, with two
  positive controls)

## 4. Open follow-up

**The fence measures 57% of what it selects, and cannot do better as built.**
A package-aware probe is required. Not started here; the coverage number and its
cause breakdown are now honest, which is the precondition for fixing it.

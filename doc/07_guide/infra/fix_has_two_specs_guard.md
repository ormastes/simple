# `check-fix-has-two-specs.shs` — the reproducer + prevention rule, made checkable

Standing requirement: **"all bug should add reproducing bug and similar bug
prevention tests."** It was stated in prose to ~20 lanes in one day and still
broke: fixes landed with no RED baseline, one lane wrote both specs *after* the
fix, and one shipped a spec that could never fail. Prose is not enforcement.

```sh
sh scripts/check/check-fix-has-two-specs.shs                 # main@origin..@-
sh scripts/check/check-fix-has-two-specs.shs BASE..NEW
sh scripts/check/check-fix-has-two-specs.shs --selftest       # fatal, 6 fixtures
sh scripts/check/check-fix-has-two-specs.shs --help
```

Verdict is the last stdout line, house convention:
`PASS — <n> commit(s) checked, 0 new violation(s) (baselined: <k>)` (n > 0) /
`FAIL — … <k> NEW violation(s)` exit 1 / `ERROR — nothing was checked` exit 2.
An empty or unresolvable range is ERROR, never a vacuous pass.

## The rule

For each commit whose subject starts `fix(`:

1. it must add or modify at least one `*_spec.spl`;
2. it must carry **two distinct** spec artifacts — a reproducer and a
   class/prevention artifact;
3. where a spec is genuinely impossible (shell/daemon defects, toolchain
   config), a `scripts/check/*.shs` guard substitutes — **only** when the
   commit touches no `.spl` product code.

## Naming convention (inferred from this repo, not invented)

A spec artifact is `*_spec.spl` or `probe_*.spl`. It is the **prevention** half
when its basename contains `class`, `detection`, `generaliz`, `regression`,
`property`, `sweep`, or `fails_closed`; otherwise it is the **reproducer**.
Read off real pairs already in `main`:

| reproducer | prevention |
|---|---|
| `u64_high_bit_ordering_comparison_spec.spl` | `unsigned_ordering_signedness_class_spec.spl` |
| `silent_default_reproducer_spec.spl` | `silent_default_detection_spec.spl` |
| `probe_wide_int_boundary_jit.spl` | `wide_int_boundary_class_spec.spl` |

## Why the prevention spec specifically

Lanes treat it as ceremony. It is the highest-yield artifact in the process — in
a single day it caught a gap its own reproducer missed six times:

- **`occurs_check`** — the fix looked right and the `T=[T]` reproducer PASSED it,
  but `TYPE_VAR_BASE`(50000) > `TYPE_NAMED_BASE`(10000) put every unbound type
  var in the named-type arm and over-reported. Only the prevention spec's
  over-report guards caught it.
- **u64 ordering** — prevention failed 6 cases to the reproducer's 3, covering
  unsuffixed `u64 > 0` (Int-typed): the pairing a UInt-only fix misses, and by
  far the commoner way to write it.
- **ed25519** — the reproducer audited only `ed_scalar_mul`; prevention swept
  every scalar-mul entry point and found the function signing *actually calls*
  was branchful too, despite a docstring promising constant time.
- **`silent_default` lint** — deleting its suppression-reason requirement left
  the reproducer 6/6 GREEN; only prevention went red.
- **a dotted-path resolver** — the repro spec passed an incomplete fix; only the
  3-segment prevention case caught it.
- **an aliased-param sweep** — found five shapes the filed reproducer missed,
  including a distinct new defect.

## Vacuity checks

Three vacuous specs shipped in one day, one guarding **crypto**. On the specs a
`fix(` commit touches, the guard flags:

- a `find()`/path literal naming a `.spl` that does not exist —
  `ed25519_ct_property_spec` searched `ed25519.spl` while the function lives in
  `ed25519_ops.spl`, so `find()` returned -1 and it could neither pass nor catch
  a regression;
- a subprocess spec asserting content without first asserting `rc == 0` and
  non-empty stdout — one shelled out to `bin/release/simple`, a 2181-byte
  production-guard wrapper that refuses the seed and exits *without* running the
  fixture; all three assertions failed on empty stdout and looked exactly like a
  live codegen defect;
- an embedded fixture string containing `{` — the **spec's** lexer resolves the
  interpolation, not the fixture's, so the file dies with `zero-examples` before
  any example runs.

## Baseline

Adopted the same way as `check-no-phantom-module-imports.shs`: fail only on NEW
violations, so it can be turned on immediately without blocking every lane on
the pre-existing backlog. Baseline lives in
`scripts/check/fix_two_specs_baseline.txt`, keyed by commit **subject** (stable
across the constant rebases here), not by sha. `--generate-baseline` rewrites
it; do not reach for it to silence a genuine new finding.

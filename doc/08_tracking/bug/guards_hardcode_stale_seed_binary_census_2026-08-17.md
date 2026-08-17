# 27 guards and gates hardcode `bin/simple`, so they report on a stale seed

- **Filed:** 2026-08-17
- **Severity:** P1 — these guards can pass BY CONSTRUCTION, and one of them has
  already been used to retire four real defects
- **Status:** OPEN

## The defect

`test/01_unit/engine_divergence/check-engine-divergence-probes.shs:37` reads:

```sh
SIMPLE="$ROOT/bin/simple"
```

Not injectable, no override. `bin/simple` is the **Rust seed**, mtime
2026-08-16 22:59. So the guard reports on that one binary no matter what the tree
contains — including after the very fix it is supposed to be checking.

## Measured consequence (by another lane, reproduced on two independent builds)

`probes/alias_value_semantics_probe.spl`, `SIMPLE_EXECUTION_MODE` pinned:

| binary | interpreter | jit | guard verdict |
|---|---|---|---|
| `bin/simple` (stale seed) | 777 | 777 | `PASS — 5 probes, 0 divergences` |
| fresh build 08:33 | **42** | 777 | — |
| fresh build 09:37 | **42** | 777 | — |

`42` is the exact value documented by the retired
`jit_class_mutation_drop_characterization` row. The divergence is real and
current; the guard is structurally incapable of seeing it.

**`e21824a4ed4` retired 4 rows on that guard's green verdict**, including
`struct_field_aliases_under_jit` and the drop-characterization row. Those
retirements rest on a measurement of a binary older than the code.

## Census — this is not one file

`/usr/bin/grep -rlE '\$\{?ROOT\}?/bin/simple' scripts/check/ test/` returns **27
files**. Confirmed members include:

- `scripts/check/check-pure-simple-pipe-lambda-parse.shs`  ← in the pre-push chain
- `scripts/check/check-stage4-memory-gate.shs`             ← in the pre-push chain
- `scripts/check/check-vhdl-gen-probes.shs`
- `scripts/check/check-sqlite-backend-acid.shs`
- `test/01_unit/engine_divergence/check-engine-divergence-probes.shs`
- `test/perf/port_algorithms/run_cipher_compress_gate.shs`
- `test/perf/graphics_2d/run_span_bench.shs`
- `test/05_perf/port_algorithms/run_cipher_compress_gate.shs`

The pre-push hook chains 53 guards. Any of them that resolves the compiler this
way is asserting a property of a binary from last night, not of the tree being
pushed. **A guard that cannot observe the change it gates is decorative.**

## Why this is the worst shape of guard failure seen today

Most bad guards fail loudly or fail closed. This one **passes by construction**,
so it manufactures a green audit trail *and* retires the defects it should have
caught. The damage compounds: the green verdict becomes cited evidence in a bug
doc, and the row is closed with a record that looks rigorous.

It is a sibling of a defect filed hours earlier against the same file
(`engine_divergence_guard_control_depends_on_fixed_defect_2026-08-17.md`), where
the guard's positive CONTROL is a defect that has since been fixed — so that
guard will go RED exactly when the codebase improves. One file, two independent
ways of being unable to tell the truth.

## Required fix

1. **Make the binary injectable**: `SIMPLE="${SIMPLE_BIN:-$ROOT/bin/simple}"` in
   all 27 sites.
2. **Fail closed on staleness**: emit `ERROR — nothing was checked` and exit 2
   when the binary predates the sources it probes. Absence of a current compiler
   is absence of evidence, not a pass. This matches the verdict convention the
   other guards already use.
3. **Reopen the 4 rows** retired by `e21824a4ed4`.
4. Audit the remaining 22 sites for the same false-green pattern; the two in the
   pre-push chain first.

## Open question the reopened rows must answer

`interp 42` vs `jit 777` establishes DIVERGENCE, not which engine is correct
under the language's alias/value semantics. Do not assume the interpreter is
right merely because it has been right in most recent cases — decide it from the
language rules and record the reasoning.

## Provenance

Guard line and the 27-file census verified directly in this checkout. The
three-binary probe table is another lane's measurement, reproduced by them on two
independent fresh builds; full detail in
`doc/08_tracking/bug/engine_divergence_guard_hardcodes_stale_seed_2026-08-17.md`
(`2d461171550`).

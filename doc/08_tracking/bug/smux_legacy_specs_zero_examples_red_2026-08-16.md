# smux legacy specs fail the zero-examples gate despite all checks passing

**Date:** 2026-08-16
**Status:** RESOLVED 2026-08-16
**Files:** `test/01_unit/os/smux_spec.spl` (+ identical mirror `test/unit/os/smux_spec.spl`),
`test/01_unit/os/smux/smux_dashboard_spec.spl` (+ mirror `test/unit/os/smux/smux_dashboard_spec.spl`)

## Symptom
`bin/simple test test/01_unit/os/smux_spec.spl` reports
`declared>=1 executed=0 passed=0 failed=1 reason=zero-examples` — permanently RED —
even though the file's own 20 checks all print `PASS` and `DONE`.

## Cause
Both files are legacy main()-style tests (`fn test_*` + `print("PASS: ...")`,
driven by `main()`), not SSpec `describe`/`it` blocks. The runner executes zero
examples and the fail-closed zero-examples gate (correctly) refuses to count a
print-based run as a pass. The print-based checks are also not real oracles — a
`FAIL` print does not fail the process.

## Unblock condition
Convert each `fn test_*` body into an `it` block with `expect`/`assert_*`
oracles (per `.claude/rules/testing.md` Modern SSpec), updating BOTH duplicate
trees identically so `check-test-tree-divergence` stays green. Verified during
the 2026-08-16 smux hardening pass; not converted then because the 2×~400-line
rewrite is independent of that change set.

## Resolution (2026-08-16)

All four files converted to Modern SSpec `describe`/`it` blocks with `expect`
oracles; no `fn test_*`, no `main()`, no `print("PASS"...)` remains. Every
original check is preserved as an example, and several were strengthened to
assert additional fields the print-based version left unchecked. Both mirror
trees are byte-identical (`cmp` clean).

The zero-examples gate is cleared — `executed` is now non-zero in all four:

| file | verdict |
|---|---|
| `test/01_unit/os/smux_spec.spl` | `declared>=20 executed=20 passed=20 failed=0 dropped=0` |
| `test/unit/os/smux_spec.spl` | `declared>=20 executed=20 passed=20 failed=0 dropped=0` |
| `test/01_unit/os/smux/smux_dashboard_spec.spl` | `declared>=21 executed=21 passed=21 failed=0 dropped=0` |
| `test/unit/os/smux/smux_dashboard_spec.spl` | `declared>=21 executed=21 passed=21 failed=0 dropped=0` |

Conversion surfaced a separate compiler defect — chaining a method off a
`static fn` factory inside a nested call fails to resolve the method — filed as
`static_factory_method_chain_wrong_value_2026-08-16.md`. Every example binds a
`val` first to work around it, and both specs carry a comment pointing at that
record.

**Evidence caveat:** these verdicts come from
`bin/release/x86_64-unknown-linux-gnu/simple`, which self-identifies as the Rust
bootstrap seed. No pure-Simple self-hosted runner exists in this tree to
cross-check them: `bootstrap/stage1|2|3/simple` have no `test` command,
`release/x86_64-unknown-linux-gnu/simple` core-dumps on `test --help`, and
`build bootstrap` terminates inside Stage 1 without a verdict.
Independently corroborated upstream by
`deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`,
which records that no pure-Simple self-hosted test evidence is obtainable
in-tree and that the re-bootstrap recovery path is itself blocked.

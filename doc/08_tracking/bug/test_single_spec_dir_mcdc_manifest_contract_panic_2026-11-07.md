# Plain `test` on a 1-spec dir panics "invalid MC/DC manifest contract"

- **ID:** `test_single_spec_dir_mcdc_manifest_contract_panic_2026-11-07`
- **Status:** OPEN
- **Priority:** P2
- **Area:** `src/lib/nogc_sync_mut/test_runner/` (MC/DC manifest handling, interpreter route)

## Repro

Windows, `bin/simple.exe` at `fe52a1431e6`, a directory holding one trivial spec:

```
describe "trivial":
    it "adds":
        expect(1 + 1).to_equal(2)
```

Command: `bin/simple.exe test <dir>` (no `--coverage`). 56 s, 332 MB peak.

Output:

```
[mcdc] SIMPLE_MCDC_MODE=on: interpreter run is not MC/DC-instrumented; running on the interpreter (use --coverage or native for MC/DC evidence)
  FAIL  ...\onespec\trivial_spec.spl (0 passed, 1 failed, 2535ms) [setup: 23ms]
        Error: error: semantic: panic: test-runner: invalid MC/DC manifest contract
SPEC FILE VERDICT: ...trivial_spec.spl outcome=ERROR declared>=1 executed=1 passed=0 failed=1 in_development=0 dropped=0
```

Afterwards the doctest pass also reports `error: test-runner: no doctest blocks found` / `SPL Doctest: 0 passed, 1 failed`.

## Expected

A passing trivial spec reports 1 passed; a missing MC/DC manifest on the
interpreter route degrades (as the `[mcdc]` line already announces) instead of panicking.

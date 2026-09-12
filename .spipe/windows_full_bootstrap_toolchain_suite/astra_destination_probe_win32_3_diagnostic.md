**Confirmed:** prepare’s destination probe misclassifies expected missing-parent error 3. No files changed or tests/probes run. I read the state and all four Astra reports.

- **Call chain:** shell preflight → `native_action prepare` → `Publish(..., true)` → `Parents(destination, false, held)` → full-path `CreateFileW`. See [producer:432](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:432), [dispatch:396](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:396), and [probe:343](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:343).
- `Parents` validates and retains root-to-existing-prefix handles, then returns at the first missing component without creation. The destination’s suffix parent and leaf therefore remain absent; probing the complete pathname yields 3, rejected at line 350. [Parents:239](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:239)
- **Evidence limit:** [state:80](C:/Users/ormas/dev/simple/.spipe/windows_full_bootstrap_toolchain_suite/state.md:80) records this path *state*, but no exact absolute failing pathname. The current focused test has no explicit safe-missing-suffix positive fixture. Its reparse case uses `$tmp/output-alias/new/receipt.env`, which should fail earlier with `ancestor.reparse`. [test:239](C:/Users/ormas/dev/simple/test/01_unit/scripts/materialize_symlinks_windows_test.shs:239)

**Semantics and minimal correction:**

- Missing leaf with an existing validated parent: error 2 means absent.
- Missing suffix below a validated existing prefix: error 3 means absent during non-mutating prepare.
- Any existing reparse ancestor: reject before destination probing or suffix creation, even if its target is valid.
- At line 350, accept 2 in both modes and 3 **only when `checkOnly` is true**: the rejection condition becomes `e != 2 && !(checkOnly && e == 3)`. Prefer reporting captured `e`.
- Publish first creates/verifies missing parents; error 3 afterward is unexpected and should remain fatal. Preserve retained handles, exclusive temporary creation, flushing, no-replace rename, and handle-based cleanup. [publication:346](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:346)

**Safety boundary:** no-follow, root-first validation with write/delete sharing denied protects existing ancestors; publish repeats validation rather than trusting prepare. Acceptance of 3 alone proves no ancestry safety. Concurrent insertion beneath the first missing component can affect prepare’s later pathname probe; prepare grants no publication authority. Created-directory create/open races remain an unverified broader limitation.

**One-shot oracle specification, not executed:** within the existing fixture harness, use exactly one `run_materializer "$destination"` invocation per row. [helper:43](C:/Users/ormas/dev/simple/test/01_unit/scripts/materialize_symlinks_windows_test.shs:43)

| Destination/setup | Expected result |
|---|---|
| `$tmp/safe/new/receipt.env`; `safe` exists, `new` absent; valid fixture | Exit 0, receipt `result=pass`; currently error 3. Separately observe prepare leaves `new` absent. |
| Existing `$receipt` | Exit 1, `receipt path already exists`, bytes unchanged. Native probe, if reached: `receipt.destination-exists`. |
| `$tmp/output-alias/new/receipt.env`; existing junction fixture | Exit 1, `ancestor.reparse`; `$tmp/real-output/new` remains absent. |

These are proposed acceptance oracles, not passing evidence.
# Collection selector bound regression: test-first evidence

Status: **BLOCKED — no executable RED or GREEN**. This is selector validation,
not proof of production CollectionPlan extraction, lowering, or execution.

## Ownership and sequence

- Owner: `/root/item3_planner`; session `01a0fedc-f802-7af2-ab5b-a5c6abe85984`.
- Worktree: `C:/dev/simple-item3-planner-20261003`.
- Branch: `work/item3-planner-20261003`; target: `release/1.0`.
- Base and observed target: `cb2f783acf0ea22e8da54ff0d8d18b4fb14c816c`.
- Tests committed before source: `944e1fe7644`.
- Source guard committed after diagnostic build attempts: `8ab6c4d7bd1`.
- Review added static-only coverage, independent of profile admission.

The unit tests cover all four policies and all four attributes for static and
admitted-profile contradictions, exact/zero boundaries, and stale unadmitted
profiles. The standalone native probe imports the real production selector.
The fix rejects inconsistent upper-bound evidence before any candidate is
selected and reports `contradictory-size-bound`; unknown bounds remain unknown.

## Diagnostic runtime identity and command

The parent identified this pure-Simple bootstrap binary (not Rust seed):
`C:/Users/user/.simple/worktrees/simple-windows-phase2/build/bootstrap-llvm80/stage2/x86_64-pc-windows-msvc/simple.exe`.
Its reported version is `simple-bootstrap 1.0.0-rc.1`. Its lineage is
**unadmitted**, and it exposes compilation rather than the required full
`test`/`check` CLI. These attempts cannot satisfy release verification.

From the owned worktree, the exact arguments were:

```text
native-build --source src/compiler --entry-closure --backend llvm --target x86_64-pc-windows-msvc --runtime-bundle core-c-bootstrap --runtime-path C:/Users/user/.simple/worktrees/simple-windows-phase2/build/bootstrap-llvm80/stage3/x86_64-pc-windows-msvc/stage2-runtime-authority --threads 2 --entry test/02_integration/compiler/collection_plan_bound_native_probe.spl --output build/item3-planner-tdd/collection_plan_bound_native_probe.exe
```

Both attempts set `SIMPLE_NO_STUB_FALLBACK=1` and `SIMPLE_CACHE_DIR` to the
owned worktree's `build/item3-planner-tdd/cache`. PowerShell `Start-Process`
used a hidden window, redirected both streams, and bounded `WaitForExit` to
120000 milliseconds; timeout stops only that owned process.

1. Initial attempt exited 1 before compilation with
   `SCV-E-ADMISSION: compile-event-journal-missing`, requesting the first-build
   cold inventory flag. Logs: `build/item3-planner-tdd/red-build.stdout.log`
   and `red-build.stderr.log`.
2. The single retry additionally set `SIMPLE_SCV_INVENTORY_COLD_INIT=1`.
   It timed out after 120 seconds and was stopped. Logs:
   `build/item3-planner-tdd/red-cold-build.stdout.log` and
   `red-cold-build.stderr.log`. Only the workaround-coverage note was emitted;
   no compiler diagnostic or assertion result was produced.

After timeout, process inspection found no remaining matching native probe
process, and `Test-Path build/item3-planner-tdd/collection_plan_bound_native_probe.exe`
returned `False`. The diagnostic process is terminal; this is not an observed
failing regression assertion. No GREEN attempt was made because the compiler
blocker remains unchanged. `git diff --check` passed for the authored delta.

## Remaining gates

Run the unit spec and native probe with an admitted self-hosted runtime,
demonstrate the expected failing assertion at the test-first commit and passing
assertions with the fix, then run compiler/core/MCP and environment guards
required by AGENTS.md. Production planner invocation and executed MIR,
cross-engine semantic parity, profiling, memory, and performance acceptance
remain outstanding. This report does not authorize release or a PASS claim.

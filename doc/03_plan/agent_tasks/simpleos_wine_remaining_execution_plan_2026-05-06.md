<!-- codex-plan -->

# SimpleOS Wine Remaining Execution Plan

Date: 2026-05-06

## Scope

This plan starts from the current audited boundary in
`doc/09_report/simpleos_wine_substrate_completion_audit_2026-05-06.md`.

Current verified state:

- The known non-GUI `hello.exe` milestone prints `Hello from SimpleOS Wine`.
- The milestone is gated by PE validation, import binding, image mapping, CPU evidence,
  x86_64 decode/dispatch evidence, modeled NT bridge evidence, and decoded stdout payload
  execution.
- The path no longer requires the earlier `SIMPLE_WINE_HELLO` fixture marker.
- The x86_64 decoder accepts the known call skeleton at the entrypoint or after a bounded
  safe entry prologue.

Out of scope for this plan:

- Calling the result a general Wine port.
- Running arbitrary PE code natively.
- Broad renderer, kernel, container, and POSIX rewrites in the same change.
- JJ commit/rebase/push work.

## Target Result

Move from a known-hello skeleton executor to a small, auditable PE dispatch substrate that can
execute the same hello behavior through decoded instruction metadata and modeled NT calls, while
preserving explicit blockers for unsupported PE programs.

## Acceptance Criteria

1. The known `hello.exe` command still prints exactly `Hello from SimpleOS Wine`.
2. The x86_64 decode plan reports instruction sequence metadata instead of relying on fixed CPU
   constants.
3. CPU execution consumes the decoder's call sequence and target metadata directly.
4. The import-binding layer remains responsible for validating decoded call targets against the
   PE import table.
5. Unsupported instructions, reordered NT calls, missing stdout payloads, and import/CPU target
   mismatches fail with structured errors.
6. The completion audit clearly states what is verified, partial, and still missing.

## Implementation Phases

### Phase 1: Decoder Plan Metadata

Files:

- `src/lib/common/wine_x86_64_decode.spl`
- `test/lib/common/wine_x86_64_decode_spec.spl`

Tasks:

- Extend `WineHelloInstructionPlan` with decoded call sequence metadata.
- Keep failure results explicit and zero-valued.
- Preserve safe-prologue support.
- Add tests for decoded sequence text, call count, and target RVAs.

Verification:

- `bin/simple check src/lib/common/wine_x86_64_decode.spl test/lib/common/wine_x86_64_decode_spec.spl`
- `bin/simple test test/lib/common/wine_x86_64_decode_spec.spl --mode=interpreter --clean`

### Phase 2: CPU Plan Uses Decoder Metadata

Files:

- `src/lib/common/wine_cpu_exec.spl`
- `test/lib/common/wine_cpu_exec_spec.spl`

Tasks:

- Populate `WineCpuHelloExecutionPlan.call_sequence` and `call_count` from the decoder plan.
- Remove duplicated fixed sequence assumptions from CPU plan construction where possible.
- Keep CPU evidence gates ordered and facet-based.
- Keep mapped entry-window gating before accepting execution.

Verification:

- `bin/simple check src/lib/common/wine_cpu_exec.spl test/lib/common/wine_cpu_exec_spec.spl`
- `bin/simple test test/lib/common/wine_cpu_exec_spec.spl --mode=interpreter --clean`

### Phase 3: Dispatch Uses Plan Sequence

Files:

- `src/lib/common/wine_hello_dispatch.spl`
- `src/lib/common/wine_nt_bridge.spl`
- `test/lib/common/wine_hello_dispatch_spec.spl`
- `test/lib/common/wine_nt_bridge_spec.spl`

Tasks:

- Route dispatch through the decoded plan sequence rather than hardcoded local symbol arrays.
- Keep the bridge sequence gate strict: `GetStdHandle`, `WriteFile`, `ExitProcess`.
- Add negative coverage for reordered, missing, or extra calls.
- Preserve byte-count, stdout-handle, and exit-code evidence.

Verification:

- `bin/simple test test/lib/common/wine_hello_dispatch_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_nt_bridge_spec.spl --mode=interpreter --clean`

### Phase 4: End-To-End Probe Boundary

Files:

- `src/lib/common/wine_hello_exe.spl`
- `test/lib/common/wine_hello_exe_spec.spl`
- `test/integration/app/wine_hello_command_spec.spl`

Tasks:

- Ensure `wine_hello_exe_probe` validates import/CPU target agreement after decoding.
- Keep malformed PE, unsupported import, image layout, CPU, dispatch, and payload errors
  separated.
- Add end-to-end coverage for sequence mismatch and safe-prologue execution.

Verification:

- `bin/simple test test/lib/common/wine_hello_exe_spec.spl --mode=interpreter --clean`
- `bin/simple test test/integration/app/wine_hello_command_spec.spl --mode=interpreter --clean`
- `bin/simple run src/app/wine_hello/main.spl`

### Phase 5: Audit And Stop Gate

Files:

- `doc/09_report/simpleos_wine_substrate_completion_audit_2026-05-06.md`

Tasks:

- Update the checklist with fresh evidence and exact test counts.
- Keep the completion decision conservative.
- Do not call the active objective complete unless a completion audit proves all Wine
  preconditions and the intended hello execution requirement are fully satisfied.

Verification:

- Wine-scope stub scan:
  `rg -n "pass_todo|pass_do_nothing|pass_dn|todo\\(" src/lib/common/wine_*.spl src/lib/common/ui/wine_x11_adapter.spl src/lib/common/pe_coff_header.spl test/lib/common/wine_*_spec.spl test/lib/common/ui/wine_x11_adapter_spec.spl test/lib/common/pe_coff_header_spec.spl test/integration/app/wine_hello_command_spec.spl src/app/wine_hello/main.spl doc/09_report/simpleos_wine_substrate_completion_audit_2026-05-06.md doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`

## Risks

- The decoder can become a second import validator if target checks drift back into it.
- Expanding instruction support can accidentally imply arbitrary native execution.
- Long-running `wine_hello_exe_spec` can hide regressions if only smoke tests are used.
- The worktree contains unrelated browser and sandbox changes; Wine edits must remain scoped.

## Stop Condition

Stop this plan when:

- all phase verification commands pass;
- `src/app/wine_hello/main.spl` prints `Hello from SimpleOS Wine`;
- unsupported and mismatch cases fail with structured errors;
- the audit report is updated with the current boundary;
- no Wine-scope stub/todo scan matches remain.

Do not mark the broader active objective complete unless a separate completion audit shows that
all Wine preconditions, not just the controlled hello path, are implemented and verified.

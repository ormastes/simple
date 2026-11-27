# Native untyped if/Result subject regression

Status: authored, NOT_RUN. No compiler fix is implemented here; HIR versus MIR versus producer miscompilation remains undetermined. This regression must not be described as a passing prevention gate before actual execution.

Original evidence: PR7511 head47c8700a692be4782cdea3ac4be129f9cdfe204d documents native Stage2 run15 failure in jit_instantiator.do_jit_compile. An unannotated `if success: Ok(code) else: Err(if has_error: error else: "Unknown error")`, followed by a bare Ok/Err match while another enum owns the same variants, loses subject/binder ownership. Explicit `Result<[u8], text>` annotation builds. Seed-interpreted HIR/MIR tests passed, so they cannot stand in for this boundary.

## Executable cases

`test/02_integration/compiler/hir/untyped_if_result_subject_cli_spec.spl` imports real process/file facades. Three source fixtures retain the colliding enum and byte-array/text payload types:

1. Original unannotated if join, nested error fallback and bare variant match.
2. Same source with explicit Result annotation, an adjacent successful control.
3. Unannotated if/elif join with the same nested fallback, testing another join shape.

Every compiled program executes success bytes7/19, explicit error text and fallback error text with distinct nonzero failure exits, then prints an exact case-specific PASS marker. Compile success alone is insufficient.

Steps: `Prepare the real fixture`; `Invoke the production owner`; `Check the observed contract`; `Check the neighboring failure case`. Setup clears only the case-owned artifact directory, copies actual fixture source, and uses an isolated cache/output. Nonzero setup/build exits and missing absolute SIMPLE_BIN assert failure; there is no skip/seed fallback. Logs and status SDN remain in `build/test-artifacts/hir-if-result/<case>/`.

## Admission and command

Pin SIMPLE_BIN to a source-matched, admitted compiler implementing native-build; pin the outer test runner independently if different. Record both binaries, source, target/runtime/tool and cache identities. SIMPLE_LIB does not change the compiled child compiler implementation. Native argv sets SIMPLE_BOOTSTRAP=1 and the original SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1; it does not lower memory reserve or disable managed tool checks.

Run once from the frozen source root:

```text
<admitted-fullCLI> test test/02_integration/compiler/hir/untyped_if_result_subject_cli_spec.spl --mode=interpreter
```

Each compile is bounded120seconds/4MiB capture; each program10seconds/64KiB; setup5seconds per child. Use the canonical outer whole-process-tree watchdog, aggregate450seconds and previously admitted RSS policy. The bounded child facade alone does not prove descendant retirement. Require terminal outer receipts, actual3 discovered/executed cases, zero skips/failures and retained exact stdout/exit checks. Refusal, timeout, unsupported provider, truncated output, missing receipt or missing runtime is not PASS. Do not rerun unchanged failures. All runtime/source-check/core/MCP gates remain NOT_RUN in this lane; no qualified runtime currently exists.

Dependency refresh 05:04 UTC: PR7511 closed as superseded by PR7536, head e11dc071418d21530309a2841a5f22e06605031f. Its unchanged OPEN untyped-if bug and annotation workaround remain; no native regression is included there. Release05c57b4368292f3df439c76cd94d4307d9311d77 includes PR7534 static-comparison typing, a separate mechanism.

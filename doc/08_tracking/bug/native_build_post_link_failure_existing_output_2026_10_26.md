# Native build fails after a successful link with an existing output

Status: OPEN; publication cause unconfirmed, diagnostic outputs preserved.
Canonical ID: `native_build_post_link_failure_existing_output_2026_10_26`.
Authoritative DB reconciliation pending: no qualified full CLI is available.

Producer SHA-256:
`acfedbebd1db457efc0f8d1b0b3020dfa20711157bc090334c1b523a6a228779`.
Source baseline: `a0aa04ea5df71665466a5c148cd148b6711da23e` plus the six
Result method-match workarounds. Windows GNU target, LLVM, core-c-bootstrap.

Two native fixture commands with `--mode one-binary` emitted both expected
objects and reported `phase=link state=succeeded`, then returned 1 without a
specific error in their captured stderr. Existing output executables from
the earlier diagnostic remained in place; the newly linked temporary output
and temporary runtime objects were removed. No SMF stage ran in these commands.
The same sources' emitted objects were strictly relinked with the canonical
C runtime and ran their behavioral assertions successfully.

Evidence directory: `C:/dev/wt-p3wa/build/native_probe/result-parameter-owner`.
Logs: `cycle3-native_wire_bool_result_parameter.log` and
`cycle3-native_wire_restore_result_parameter.log`. Preserve the `.link-command.txt`
files and the `cycle3-*-manual.json` manifests. These commands remain failed;
manual executable success does not repair publication or admission.

Investigate `src/app/io/_CliCompile/compile_targets.spl` around the staged-output
rename and `native_build_finish_intermediate`, plus `_cli_file_rename_impl` on
Windows. A destination-replacement failure is a hypothesis, not a proven cause.
Regression must distinguish fresh destination, existing inactive destination,
and an output held open by another process; preserve the old good executable
and report the actual failed operation. Do not weaken the fresh-output guard.

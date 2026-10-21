# Controlled Result observation manual

Status: **AUTHORED / UNRUN**. Manually authored from the executable SSpec; spipe-docgen was not executed.

Executable: `test/02_integration/compiler/mir_opt/result_abi_observation_capture_spec.spl`.

1. Create real MIR metadata and invoke canonical builtin registration. Check independently derived Result identity and Ok/Err tags.
2. Capture internally typed Ok and Err for zero, negative one, and both signed i64 bounds. Compare both actual payloads and tags.
3. Supply a wrong expected owner or unsupported tags to the controlled wire boundary. Require precise refusal without a successful payload projection.
4. Alter actual registration maps: absent, extra variant, tag mismatch, and shadowed owner must refuse.
5. Copy each actual projection and change owner, tag, or payload. Require the corresponding raw diagnostic for each outcome.
6. Remove, swap, or rewrite source outcomes. Require coverage/source refusal independently of target projections.
7. Feed actual observations to the unchanged qualified validator with no authority and checked=false. Require refusal and no certificate; no fabricated proof labels are supplied.

The native control `test/04_smoke/result_abi_raw_capture_native.spl` uses the same production capture and comparator. Its output explicitly remains unauthenticated/not checked. It requires a producer/runtime built and qualified from these images; an old compiler's behavior is not evidence for this change.

No execution, branch coverage percentage, proof checking, or runtime refinement is claimed. See the linked plan at `doc/03_plan/sys_test/c7_result_abi_raw_capture_20261020.md` for remaining C7 obligations.

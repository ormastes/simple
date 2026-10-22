# Signed build reuse lacks a protected GitHub observation path

**Status:** Open. No required GitHub build check may report local reuse yet.

`src/app/build/signed_build_controller.spl:15` composes the gate, signature
and private-artifact checks, but its caller must supply the exact candidate
expectation and independently observed `GateReceipt`. The protected gate
provider (`src/app/build/signed_build_gate_provider.spl:76`) validates all
bootstrap obligations from pinned manifest bytes; it does not collect those
observations. There is no wire parser or protected GitHub event/merge-candidate
collector for `GateReceipt`, and `.github/workflows/build-binaries.yml` still
runs the ordinary Linux Stage 2 build without calling the controller.

`src/app/build/signed_build_ci_observation.spl` now rejects inconsistent
caller-supplied current PR, merge-tree, protected identity, manifest and gate
digests before that controller runs. New `gate_receipt_wire_v1.spl` and
`signed_build_ci_wire_adapter_v1.spl` draft a bounded decoder and fallback
bridge, with focused specs and Astra static review. Their Simple tests remain
unrun under the current verification cap. Neither module collects or
authenticates observations; the protected collector and workflow wiring below
remain open.

**Unblock owner:** GitHub admission workflow owner, after the current dirty
workflow lane hands over edit ownership. Build an immutable verifier from
approved base-owned source; derive repository, PR, base, head and actual
integration-candidate tree independently; obtain protected gate observations
and signer/revocation policy; retrieve untrusted receipt/signature/artifact
into isolated storage; call the V2 controller. Only its `REUSE` private path
may replace the Linux Stage 2 build step. Every missing or invalid input runs
the ordinary build, and the existing job must still report its result. A
candidate-authored gate receipt or local signature alone is insufficient.

**Required evidence:** fork PR, changed base/policy/checker, missing or failed
mandatory row, stale/revoked signer, wrong candidate/target/submodule pin,
artifact mutation after download, valid private-copy reuse, and full-build
fallback, all under the existing unprivileged Stage 2 job. The smoke/upload
steps and required context must run in both branches.

# Managed parser V2 admission

Source-authored interface, runtime qualification UNRUN. V2 support requires the
reviewed worker/result/runner changes together; this guide does not certify a
producer or authorize a launch.

The trusted qualification owner independently supplies the issuer digest,
receipt digest, worker image/path, exact frontend identity and target. Do not
copy expected values from a submitted manifest or from the qualification
receipt being admitted. An issuer image hash alone is not a signature.

The explicit production route is `grouped-run-v2` with all these options:

| Option | Independent input |
|---|---|
| `--manifest` | Absolute run file path |
| `--receipt` | Absolute existing qualification receipt path |
| `--receipt-digest` | Trusted qualification owner receipt SHA-256 |
| `--issuer-digest` | Independently pinned issuer executable SHA-256 |
| `--worker` | Independently pinned absolute worker image path |
| `--worker-digest` | Independently pinned worker SHA-256 |
| `--frontend-identity` | Canonical single-line nine-string SDN identity |
| `--target` | Exact admitted target triple |
| `--target-os` | Expected runtime target OS |
| `--target-arch` | Expected runtime architecture |
| `--target-cpu` | Expected runtime CPU selector |

Duplicate, missing, empty and unknown options reject. The direct
`grouped_run_v2` API requires the same independent pins and invokes
`managed_parse_run_admit_v2` before execution. V1 calls must reject warning mode
and the V2 identity environment key; V2 does not silently downgrade.

Frontend identity preserves the actual parent executable/source identity,
SHA-256 of its full validated prior cache scope, explicit feature digest and
capture policy, and owned flat/result/diagnostic versions. The run's environment
must transport that exact identity once, and explicitly provide arena,
entry-closure, debug-match and capture-policy settings. Snapshot/profile/action
and binding cache identities must all equal the key derived from frontend
identity, worker digest, OS, architecture and CPU.

The qualifier accepts `qualify-v2` with the existing task/workspace/root/runtime/
issuer/target/parent/parent-digest positional arguments followed by exactly one
policy (`error`, `warning` or `off`). This source supports the strict parent
profile arena empty, entry-closure `1`, debug-match empty. A fresh native worker
build and actual executed parent/worker evidence precede issuance. V2 policy
evidence is bound to its exact policy; old V1 evidence cannot certify V2.

See [authority design](../../05_design/managed_parse_warning_authority_v2_20261019.md)
and [contract scenarios](../../06_spec/01_unit/compiler/driver/managed_parse_compatibility_v2_spec.md).

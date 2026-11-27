# Host service private receipt verification

Status: **NOT_RUN**. Source scenarios are in
`test/02_integration/lib/host_service_private_receipt_v2_spec.spl`.
These are native Windows tests, not Linux scripted-provider qualification.

An administrator must provision `SIMPLE_HOST_RECEIPT_PRIVATE_PARENT` for the
test service principal with the native owner's protected private DACL contract.
Provision `SIMPLE_WINDOWS_PRIVATE_FOREIGN_READ_ROOT` separately with a foreign
read ACE. Missing fixtures or running on another OS fails; no skip or permission
repair turns the test green. Test-created children and interrupted stages remain
available for inspection and explicit administrator cleanup.

| Requirement | Actual assertion |
|---|---|
| HOST-RECONCILIATION-PRIVATE-01 | Publish through native stage/seal/no-replace, independently reopen final through private handles, compare exact bytes, then repeat and require the same immutable destination. |
| HOST-RECONCILIATION-PRIVATE-01 | Install wrong bytes at the expected final name using the actual private owner; publication must reject and leave the original bytes unchanged. |
| HOST-RECONCILIATION-PRIVATE-02 | An actual foreign-read ACL root must fail admission. Any returned cleanup capabilities are retained and closed through the native owner. |

The production reconciliation turn carries pending native cleanup and withholds
quarantine acknowledgment. The persistent caller must retain that whole turn and
use its cleanup-aware retry port. These tests do not inject native close failure;
that native-owner fault qualification remains a separate required check.

Durability is `process-crash-v1`. No Windows directory power-loss barrier is
claimed. All local verification processes must share CPU affinity `0-4`, at most
five aggregate CPUs; no build or execution was performed for this checkpoint.

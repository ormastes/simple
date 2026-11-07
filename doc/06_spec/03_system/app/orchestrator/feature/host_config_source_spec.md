# Direct HostConfig source boundary

Status: **NOT_RUN — awaiting verification**. This is an authored scenario manual,
not generated execution evidence or a native/admitted PASS.

- Spec: `test/03_system/app/orchestrator/feature/host_config_source_spec.spl`
- Oracle: `test/fixtures/orchestration/host_config_source_native_probe.spl`,
  `host_config_source_checks()`
- Fixture: `test/fixtures/orchestration/host_local_config.sdn`
- Authored requirement labels: HOST-01, CFG-01, CFG-02, from
  `doc/02_requirements/feature/caret_distributed_orchestrator.md`. This mapping
  states partial assertion intent, not completed requirement verification.

## Setup

Run the spec or compiled diagnostic from the repository root so the bounded
regular-file reader can load the fixture. The probe imports the HostConfig
source decoder directly. It does not import ResourceSet or a provider and does
not need a compiled metadata CLI to decode this fixture.

The fixture uses indented SDN with numeric maintenanceIntervalMs 100 and
maximumJournalEvents 10000. Numeric fields are not changed to strings to avoid
a compiler/parser defect. The fixture names administrative references and
paths; decoding them does not open those paths or enroll a host.

## Scenario: decode administrative intent through the direct entrypoint

1. Read the fixture with a 1 MiB bounded regular-file read and call
   `decode_host_config(source)`.
2. Check physicalHostId `machine`, serviceScopeId `user`, CPU ceiling 2000
   millicores, memory ceiling 4294967296 bytes, maintenance interval 100 and
   maximum journal events 10000.
3. Parse and canonicalize the same source using the shared SDN serializer.
   Decode that canonical text through the same direct entrypoint.
4. Compare maximumJournalEvents and journalRoot to the first decoded config.
   This checks source/value boundary parity without a ResourceList dispatcher.

## Scenario continuation: reject malformed or ambiguous source

| Input change | Required assertion |
|---|---|
| Incomplete opening mapping | Decoder returns an error |
| Repeat controllerRef with another value | `duplicate_key` at `spec.controllerRef`, positive source line |
| Add privileged:true under spec | `unknown_field` at `spec.privileged` |
| Change kind to Pod | Decoder returns an error |
| Raise maximumJournalEvents to 100001 | Decoder returns an error |
| Supply 524289 copies of the two-byte character é | Confirm 1048578 UTF-8 bytes; reject with `host_config_limit` |

The byte ceiling is checked by common.string_core.str_len before source parsing.
The oversize oracle distinguishes UTF-8 byte length from character count. The
source wrapper then uses the strict shared parser and existing value decoder;
its presence does not change the original typed configuration semantics.

## Assertion mapping and limits

| Authored labels | Concrete assertions |
|---|---|
| HOST-01 | Physical/service administrative references and budget/maintenance values decode intact |
| CFG-01 | Direct source and canonicalized source preserve the checked typed values |
| CFG-02 | Malformed, duplicate, unknown, wrong-kind, out-of-range and byte-oversized inputs fail |

Assertions stop on unreadable fixtures or rejected valid input. Schema validity
is not enrollment authentication, native host identity, available capacity,
resource enforcement or execution authority. This probe has not executed with
an admitted runner here. Generated manual checks, coverage and host/provider
integration remain NOT_RUN; no compiler repair or full-system PASS is implied.

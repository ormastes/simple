# Caret configured SSH gateway

Source `test/03_system/app/orchestrator/feature/caret_configured_ssh_gateway_spec.spl`.
Status `AUTHORED_NOT_RUN`.

Install a real controller gateway authorized for `inspect` and retain one
known controller intent. Supply an explicit shared SDN server config,
context, server alias, protected SSH profile and canonical read-only gateway
request via the five `SIMPLE_CARET_SSH_ACCEPTANCE_*` variables in the spec.
The profile must match the selected server's authentication and trust
references. Keep the fixture files under the dedicated operator's control.

The scenario invokes the Caret Suite dispatcher's `remote` action. It checks
that the authenticated gateway responds for the exact controller and request
UID and that the receipt carries no runtime execution authority. A missing
fixture or a refused remote reply fails the case.

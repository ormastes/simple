# Rebuilt CLI executes the inspected SimpleOS route

**Manual draft. Execution, captures, docgen and maintenance scan are
TEST_BLOCKED pending an admitted full CLI and real kernel/media/QEMU artifacts.**

Source: `test/03_system/os/feature/qemu_sealed_cli_route_acceptance_spec.spl`.
Requirements: platform REQ-001, REQ-014, REQ-016; named dispatch AC-N3.

## Prepare real prerequisites

Use an isolated repository checkout on the actual Linux or Windows host, with
its supported shell/environment tools and QEMU installations. Set
`SIMPLE_QEMU_CLI_ACCEPTANCE_BIN` to the full Stage4 candidate whose adjacent
`.provenance.env`, producer, parent compiler, source snapshot, build log and
essential-tools smoke log satisfy the existing canonical Stage4 verifier.
Prepare the real catalog kernels and media through their normal build/image
owners. The test does not create receipts, kernels, images or a substitute
QEMU. Installed bootstrap seeds may remain; OS builds must honor the explicit
admitted self-hosted compiler instead of discovering a seed.

The suite invokes canonical provenance verification once as its full-CLI
prerequisite, then separately exercises the production compiler selector with
that explicit compiler and a different alias. This establishes selection
precedence using a real admitted artifact. Version text alone is insufficient.
It also rejects a missing primary despite a valid admitted alias, and verifies
that the admitted alias is selected when the primary is absent. The missing
path is checked absent under this run's evidence directory before the call.
An existing version-authority SDN file is also rejected as an explicit
compiler despite the valid admitted alias. No false receipt is constructed.

The warm-cache regression calls the actual build owner twice in one process:
first with the admitted compiler and real default kernel, then with a missing
explicit compiler while retaining that same kernel. The second call must
reject the override. This checks that persistent-cache reuse remains behind
current compiler admission; a prior successful target cannot bypass it.

The GUI-mode negative matrix invokes the real CLI for both inspection flags
on all five routes. Each must produce the exact unsupported-mode diagnostic
before build or run output. No kernel or QEMU result is substituted.

## Inspect and run each route

Five scenarios cover default x86_64 and the represented named routes:
`x86_64-q35-pure-nvme-perf`, `x86_32-initrd-fat32-smf`,
`riscv64-virtio-fat32-smf`, and `riscv32-virtio-fat32-smf`.

For each route, require its actual kernel, filesystem-wrapper admission where
applicable, media and sealed plan. The canonical QEMU host-admission command
must execute its real TCG/QMP probe. The real host must be Linux or Windows,
and the CLI's reported host must match that detected host. The probe's QEMU
digest and version are checked against the planned executable, whose digest
must remain unchanged through execution. The admitted CLI provenance digest
is retained and rechecked too. Missing prerequisites produce
`MissingEvidence`, including the currently unresolved x86_32 executable-policy
boundary; an absent dependency never becomes a skipped or inferred pass.

Invoke the admitted binary's `os run --show-plan` and `--print-command`.
Compare their image digest, seal, plan digest and rendered command with the
production plan built from the same real artifacts. Invoke its actual `os run`
route, retaining stdout/stderr/status. Its existing build owner may reuse a
canonical cache or rebuild; no cache stamp is forged. The kernel digest must
remain unchanged across this inspection/run observation. If compilation runs,
its logged compiler must be the pinned admitted identity.

## Distinguish CLI and guest evidence

A zero CLI status and matching logged launch command establish host CLI-route
evidence. They do not independently observe the QEMU process's argv; the
separate host-process dispatcher fixture covers ordered argv delivery.

Extract the actual serial section separately. The default route must satisfy
the existing `test_os` SimpleOS-banner smoke oracle. Each named route must have
a nonempty canonical marker set and pass the existing scenario serial
acceptance function, including resident-fallback rejection where applicable.
This is the catalog's bounded completion evidence, not full OS or native
accelerator qualification; protection-hardening qualification is separate.

Receipts are retained under
`build/test-artifacts/os/qemu-sealed-cli-route-<pid>/`: CLI identity/provenance
hashes, full-CLI admission, and each route's QEMU probe, inspection, command and
run process results. No such captures have been produced yet.

## Resume

With the admitted runtime and artifacts available, execute this spec once in
interpreter mode, run `spipe-docgen` with `--output doc/06_spec --no-index`, then
`sspec-maintain scan` and review the generated manual/captures. Run hosts
separately; Linux evidence does not qualify Windows. Retain the exact source
candidate identity alongside the canonical compiler provenance: the existing
Stage4 source-root contract does not independently fingerprint `src/os`.

# Process arena callback closure completion (#2980)

Frozen failing source: f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c.
Producer C36: 5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235.
The actual env_access_host (74 HIR modules) and rt_hal_isolated_host (48 HIR
modules) consumers failed MIR on eleven unresolved callback methods in
process_task_arena.spl. The narrow earlier ARM/RISC-V fixture remains valid but
does not qualify these broader closures.

The eleven failures correspond exactly to unwrapped field calls at baseline
lines 147, 153, 162, 238, 239, 260, 262, 346, 366, 367, 370. The original
workaround covered only join_exact_until and host_install. This completion
uses `(host.field_fn)(...)` for those remaining calls and annotates seven
owner locals as RtHalIsolatedHostPort. No call order, arguments, branching,
return values, lifecycle rules, or cancellation behavior change. These eleven
calls return scalar bool/i64; no extra record-return helper is introduced.
The existing join record call remains unchanged.

The real process_arena_callback_fields fixture imports this production module,
installs a callback-bearing host, registers an adapter, claims the controller,
spawns/cancels a comparison, spawns/joins a replay, leaves a comparison pending
for shutdown cancellation, and checks idempotent shutdown. It asserts all
callback counts, forwarded scalar/record arguments, exact handles, join digest
fields, and both cancel/close paths. A typed fixture join helper retains the
already-established record-return workaround.

This is a source compatibility patch, not the permanent producer repair.
273368975dae610a1cf0c07ac6c14ddc3260d3bb (indirect return/owner) and
e2b959978416b265bc637c44213e01f4f91e01fa (method-field layout owner) still need
producer integration and native qualification. Distinct SDN Array/Dict payload
mismatches in env_access_host are not hidden by this scope.

Validation pending: independent source review, actual changed-file native
object and actual fixture execution. No complete consumer, full build, release,
or performance success is claimed. Evidence owner is manual_object_qualification.
No expensive run is authorized until the parent admits resources.

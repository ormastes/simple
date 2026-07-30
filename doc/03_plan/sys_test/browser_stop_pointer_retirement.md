# Hosted Stop Pointer Retirement Test Plan

## Scope

Verify the hosted renderer's real deferred-Stop scheduling boundary. Stop must
leave the committed page and retained image resources intact, retire parent and
worker pointer ownership, and reject a release belonging to the retired press
before it can produce pointer-up or click behavior.

## Traceability

| Requirement | Evidence |
|---|---|
| REQ-WEB-BROWSER-008 | Stale release is rejected at the parent input boundary. |
| REQ-WEB-BROWSER-009 | Deferred Stop activates after the partial write drains. |
| REQ-WEB-BROWSER-014 | Parent and sandboxed worker ownership are checked separately. |
| REQ-WEB-BROWSER-018 | Stop preserves committed page/resources while retiring transient press state. |
| REQ-WEB-BROWSER-021 | Executable SSpec and matching manual share the four named steps. |

## Scenario

1. Prime a committed worker page, parent retained image, parent press/cancel
   state, worker press state, and a partially written older parent command.
2. Submit Stop, complete the older write, and activate the deferred Stop.
3. Decode the actual Stop wire and dispatch it through the worker handler.
4. Submit the old release and assert exact rejection plus unchanged wire and
   request sequence, proving no pointer-up command or worker click path ran.

## Execution Gate

Run only with a source-matched admitted pure-Simple full CLI. A seed compiler,
bootstrap result, source inspection, or stale executable cannot promote this
scenario to executed PASS.

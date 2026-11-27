# Windows request-local cleanup control deadline

Status: **SOURCE-ONLY NOT_RUN**. No compiler, build, test, native Windows
process, Docker command or governor/deadline execution was run for this slice.
The authored requirement association REQ-WDP-011 needs integration with the
shared control-authority requirements.

Provider control accepts only stop/destroy and a ContainerControlDeadlineV1.
After the retained request/scope binding, actual engine identity and exact
managed-object inspection, it samples the actual native wall clock and validates
request digest, original operation ID, action and expiry through the shared
control-deadline helper. The same absolute expiry is passed to the admitted
clean-environment process facade, whose native owner rechecks after governor
admission and before process entry/ResumeThread. No control context is persisted
or derived from a retained launch grant. A no-effect stop also validates an
explicit context. Unknown actions fail without an effect.

The adapter requires full active retained authority, rejects recovery-only
candidates, refreshes native host/provider binding and dispatches control. A
confirmed exact destroy retires that authority. Legacy explicit retained
apply(stop/destroy) keeps its existing behavior without fabricating a fresh
grant. Expiry blocks a new cleanup effect; it does not kill work automatically,
change retained phase, prove absence, or release resource accounting.

Authored actual-scripted-provider scenarios establish the intended command
ordering: the final clock is expired after engine/inspection observations and
the next stop command is not consumed (cursor 12 to 14). Digest/operation/action
mismatches likewise consume guard observations only. A separate fresh cleanup
context admits exact stop/rm commands at clock 3000 after the old launch grant
expired at 2000. Successful stop context is not reusable for a later expired
destroy; no rm is consumed, and the retained state remains exited. Clock values
are explicit synthetic observations; they do not claim elapsed native time or a
real expiration during a Docker call.

Native qualification must separately observe the real admitted Windows clean
environment owner rejecting expiry after an actual governor wait and immediately
before native workload entry. Script cursor assertions and source inspection
cannot establish that OS timing behavior. No raw stream/capture/common files
were changed by this control slice.

# Neutral provider CLI owners

Caret's adapter types and pure planning implementation now live under
`std.common.contracts.provider_cli`. The genuine contained-probe and selection
implementation lives in `std.nogc_async_mut.llm.provider_cli_container_probe_v1`.
The original three application modules are compatibility reexports, preserving
one nominal type identity rather than converting application records to library
records. Only import paths change in the moved implementations.

The probe module deliberately retains its existing Container and IO family
imports. It does not import Host or application code. A future Host coordinator
can consume it from above Container without introducing a Container-to-Host
dependency. No generic configured-library fallback is changed.

Opaque receipt/selection construction remains confined to the original producer.
Its actual capture evidence, pending cleanup and defensive diagnostic copies are
unchanged. Public snapshots remain DATA. The collector still observes an already
admitted probe; it does not authorize its first start. A complete AgentSession
coordinator must enforce fixed probe arguments before execution, retain the actual
selection on the existing Host owner and verify full invocation authority.

This extraction does not implement TaskRef content access, invocation grants,
workspace/credential preparation, selection consume/resume or interactive terminal
handoff. The generic AgentSession execution guard stays in place. Source review
and authored compatibility specifications do not establish runtime qualification;
compilation, native capture and container execution remain **NOT_RUN**.

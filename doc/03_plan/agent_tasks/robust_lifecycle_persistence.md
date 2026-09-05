# Robust Lifecycle Persistence Agent Tasks

## Lane

| Work | Owner | Status |
|---|---|---|
| Requirements and convention correction | Codex merge owner | complete |
| Pure model and validation | Codex merge owner | complete |
| Unit and SPipe evidence | Codex merge owner | diagnostic pass; pure-Simple rerun pending |
| Generated manual review | Codex merge owner | complete; 108 lines, 0 stubs |
| Lower-model sidecars | N/A | Narrow convention cleanup with one coherent API |
| Final reviewer | Codex normal/high-capability pass | implementation reviewed; final verify pending |

Shared interfaces: `LifecycleGraph`, `LifecycleTransition`,
`RecoveryRegistration`, and the six validation functions listed in the design.
Manual steps: `Define an ordered lifecycle graph`, `Reject an unsafe lifecycle
dependency`, and `Validate transition and recovery metadata`.

# Darwin launch and peer observation transport — native evidence

Executable spec: `test/03_system/check/sosix_darwin_broker_transport_spec.spl`.
Native driver: `scripts/check/check-sosix-darwin-broker-transport.shs`.

On Darwin 25.5.0 arm64, the driver compiles and hardened-signs a disposable
fixture. The helper sends one fixture protocol byte only after
kernel PID/version validation. The controller checks GetJob arguments, current
CDHash by audit token, and pinned kernel unique identity before observing data; this does not attest original launch configuration.

| Adversarial action | Required observation |
| --- | --- |
| Wrong PID, PID version, or expected CDHash | Peer observation refused |
| Modified expected GetJob argv or pinned unique ID | Peer observation refused |
| Same UID and exact executable, unrelated process | Peer observation refused |
| Exec on an already authenticated socket | Stale incarnation refused |
| Remove and recreate the same job label | Old pinned handle cannot rebind |
| Attacker-owned endpoint pathname | Helper sends zero protocol bytes |
| Wrong admission CDHash | Constructor never enters |
| Rename different signed executable onto launch path | Constructor never enters |
| Execute replacement without binding | Constructor enters (working control) |
| Asynchronous registration removal | No tree-empty or reap receipt claimed |
| Recreate label with env before first observation | Observation succeeds but original admission is unavailable |

Validation on 2026-10-29: native checker PASS. Modern SSpec PASS, one file and one
example; authorized P1 Rust bootstrap seed, interpreter mode, SIMPLE_LIB=src,
no cache/database/session daemon, sequential and assert-ran. No compiler or P2
rebuild. An initial sparse-worktree wrapper attempt lacked src/lib and executed
zero examples; after materializing src/lib the spec executed and passed.

The initial-label-takeover control demonstrates a real admission gap; GetJob hides
changed environment. The API exposes observations only, never trusted admission.
This is transport evidence only. No production V4 provider capability is
advertised, and higher-level closed admission, confinement, budgets, and full
reaping remain unqualified.

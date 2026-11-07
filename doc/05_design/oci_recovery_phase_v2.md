# Recovery of an immutable creation receipt

The common Linux adapter previously compared the caller's retained creation receipt to the provider's current intent including mutable phase. A successful native recovery persisted running/exited/stopped, so a second recovery using the original created receipt failed despite unchanged request and identity.

The repair separates immutable identity comparison from this narrow phase allowance. Every original exact-identity/exact-phase path remains unchanged, including legacy reconciliation, prepared empty-native-ID discovery and destroyed tombstone reconciliation. A phase difference is accepted only for expected CREATED and retained RUNNING, EXITED or STOPPED, with canonical full64 IDs on both sides and a second strict V2 retained-request accessor proving the same identity and phase. There is no fallback to legacy for this allowance. Changed payload, corrupt binding, operation, scope or identity remains refused.

Created-to-destroyed is refused. Matching destroyed tombstones return the existing tombstone reconciliation without native adoption or independent absence proof. Provider inspection and phase-transition validation remain unchanged; no journal or schema changes are introduced.

Status: AUTHORED / UNEXECUTED. Six focused cases use the actual common API over explicit scripted managed providers; no build, checks, native runtime or performance result is claimed. See the matching unit specification manual.

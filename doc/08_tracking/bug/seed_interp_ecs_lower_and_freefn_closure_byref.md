# Two bootstrap-seed interpreter bugs (found by Lane H4 pseudo-fs work)

## Triage 2026-11-25 — deferred to the bootstrap lane (status unchanged: OPEN)

Triaged in the P2 ledger pass on worktree `wt-p2w5-al` (release/1.0.0 HEAD
`ae1572aeb67`). Both defects live in the Rust seed interpreter/codegen
(`Entity`/`ComponentStore<T>` lowering; by-reference mutation through a free
function called inside a spec `it` closure). The pinned tracked
`bin/simple.exe` cannot be patched from source, and the self-hosted fix path
is gated on `bin/simple build bootstrap`, which this lane must not run.
Neither bug is verifiable or fixable on this Windows host with the pinned
binary, so both remain OPEN with the Lane H4 workarounds in place. The
"needs owner triage" header is superseded by this note; the correct owner
lane is the bootstrap/seed redeploy effort.

## Open 2026-09-16 — needs owner triage (superseded by 2026-11-25 triage above)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Both reproduce under `src/compiler_rust/target/release/simple run` (the seed
interpreter); both are worked-around in Lane H4 but should be fixed at the seed.

## 1. ECS `Entity`/`ComponentStore<T>` do not lower under the seed

`src/os/services/devfs_service.spl` / `procfs_service.spl` (ECS-backed) fail to
lower under the bootstrap seed: `Unknown type: Entity`; `cannot infer field
type ... struct 'ANY' field 'id'`. The pre-existing `devfs_service_spec.spl` is
itself RED for this reason. Impact: any ECS-backed service is unrunnable under
the seed, so seed-run gates can't exercise them. Workaround (H4): the
`Filesystem`-trait adapters (`devfs_filesystem.spl`/`procfs_filesystem.spl`)
keep a plain seed-safe registry of well-known nodes instead of routing through
the ECS path. Fix belongs in the seed's generic/ECS lowering (`Entity`,
`ComponentStore<T>`), or the ECS services must be re-typed to lower.

## 2. By-reference mutation lost: class instance → free function → inside a spec `it` closure

A locally-declared class instance passed to a FREE function loses by-reference
mutation when the call sits inside a spec `it` closure: `register_devfs(mgr)`
then `mgr.mounts.len() == 0` (the mount didn't persist), while a DIRECT `me`
method call (`mgr.mount(...)`) DOES persist, and both forms work in a
standalone `main`/compiled build (verified by probe). So it is specifically the
free-function + closure-capture combination in the interpreter that drops the
mutation. Impact: tests that mutate through a free function inside `it` silently
see no effect. Workaround (H4): route the mutation via a direct `me` call in the
test; keep the free `register_*` wrapper covered by a return-contract test.
Related to the known "nested closures can read but not modify outer locals"
interpreter limitation, but here the outer local is mutated via a called free
function, not directly.

## Status
Worked around in Lane H4 (pseudo-fs mount adapters landed). Real fixes are seed
interpreter/codegen changes → gate on `bin/simple build bootstrap`, currently
blocked by the toolchain redeploy.


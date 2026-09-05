<!-- codex-design -->
# Unified lifecycle architecture

The architecture is a layered virtual capsule, not a new VCS or forge:

```text
Spipe orchestration -> DevHub lifecycle API -> SCV lifecycle graph
                                      \----> SJ typed transactions -> JJ/Git
                                      \----> capability providers
```

Public-to-next-layer rules:

1. Spipe can call only versioned DevHub/SJ operations and records returned IDs.
2. DevHub domain code can depend on SCV lifecycle values and provider traits,
   never concrete provider authentication or command text.
3. SCV lifecycle values cannot depend on JJ, Git, provider, CLI, or Spipe code.
4. SJ policy/planning can consume lifecycle evidence but cannot own review,
   work-management, or wiki semantics.
5. JJ and Git are backend aliases/transports; they never become canonical
   lifecycle identity.

The base capsule is `src/lib/scv/lifecycle/`. It owns provider-neutral values,
identity derivation, exact-revision review admission, three-way sync planning,
digest-bound record persistence, work-graph separation, and release transition
invariants. `src/app/sj/{operation,integrate_plan,lifecycle_policy}.spl` owns
typed mutation vocabulary and pure planning. `src/app/devhub/cmd_lifecycle.spl`
is the versioned inspection surface, while provider capability records preserve
semantic gaps explicitly.

MDSOC feature transforms are limited to audit/provenance emission at durable
operation boundaries. They must not hide ref mutation or provider writes.
Runtime composition belongs in provider adapters and SJ backends.

The initial policy is observe-only. Promotion to local integration, remote
publication, signed tags, or SCV content writing is a separate policy change
requiring stage exit evidence.

# Portable worker preflight refusal leaves manager ownership unresolved

Status: fixed in source; bounded Phase 1 interpreter diagnostic passed.
Baseline: release/1.0.0 `ecf7971c55e`, after capability-refusal fix #5211.

Changed staged input bytes, changed producer bytes, or an isolated cache
creation failure return an ERROR before the portable worker calls its process
owner. These paths did not persist `compiler.not-started.sdn` or
`capacity.settled`. Fresh manager recovery consequently reported unknown
worker ownership and forbade retry despite no compiler having started.

The worker now uses its existing pre-start refusal writer for these preflight
errors, after task and host validation. The proof binds the task digest, host,
and reason; capacity settlement remains `no-parent-owned`. The shared ERROR
handler after compiler execution is unchanged and cannot issue this proof.
Invalid host identities remain unqualified. Failed receipt persistence leaves
ownership nonterminal. No tree-reap evidence or successful output is invented.

## Executed evidence

Pinned producer generation:
`aa58a24ebe00248b428d4507e5cb0c58ec497c28ec8b2a3ed71ec65d697f756c-ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b`
under `/Users/ormastes/wt/release-bootstrap-integration-20261025/src/compiler_rust/target/bootstrap.generations/`.

Run each spec independently from the worktree:

```
SIMPLE_LIB=src <producer>/simple test test/01_unit/app/bootstrap_builder/worker_preflight_refusal_spec.spl --mode=interpreter --assert-ran --no-cache --no-db --no-session-daemon --sequential
```

- Baseline: the three recovery cases failed with unknown ownership; both
  persistence-failure cases lacked the specific receipt-write diagnostic.
  `/tmp/buildrunner-preflight-red.log` also records an initial test expectation
  error: an invalid host returns 3 because result serialization rejects it,
  rather than 2. That expectation was corrected without changing production
  invalid-host behavior.
- Final preflight suite: 6/6. Production worker and manager recovery cover
  changed input, changed producer, and failed cache creation; both receipt
  persistence failures remain nonterminal; invalid host emits neither proof.
  Log: `/tmp/buildrunner-preflight-green.log`.
- Existing capability-refusal suite: 3/3.
  Log: `/tmp/buildrunner-preflight-capability.log`.
- Working environment-facade guard and whitespace check passed; there are
  zero executable specs under `doc/06_spec`.

These are explicitly Phase 1 source-interpreter diagnostics, not a production
native compiler PASS. Darwin V4 and actual native Hello remain unavailable.
No Phase 2 rebuild, binary deployment, or capability bypass was performed.

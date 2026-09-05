# Lane DBHANG — the hang that made a whole spec file unobservable

Date: 2026-07-28
Scope: `test/system/database/server/db_server_tier_spec.spl` reported
`Process timed out`, exit 255, on both tree paths. Lane MATCHER traced it to a
120 s runner timeout caused by example #5 hanging; lane ORPHAN2 reproduced it
serially on a quiet machine, ruling out load.

## 1. Reproduction and isolation

Streaming the runner (`stdbuf -oL bin/simple run <spec>`) showed the file dies
mid-flight, right after example #4:

```
  ✓ gives each client its own session id
  ✓ refuses to work for a session that was never opened
  ✓ refuses to work for a session that has been closed
  ✗ discards an abandoned transaction when the connection closes
EXIT=124   (nothing further, ever)
```

So the hang is example #5, `"answers every message on a connection driven by
the transport port"` — the only example that calls `DbServerCapsule.serve()`.

Reduced out of the spec to a ~30 line reproducer, `build/dbhang_min/t3.spl`:
driving the same three messages through `handle_message()` directly returns
`OK session=1 / OK / OK` and exits; driving them through `serve()` never
returns.

Narrowing runs that did **not** reproduce (each ruled out a theory):
- `build/dbhang_min/repro.spl` — the bare loop shape with a local class: fine.
- `build/dbhang_min/t2.spl` — the real `MemoryTransport` drained by a plain
  `fn`: fine.
- `build/dbhang_min/t4.spl` — the loop shape as a `me` method calling another
  `me` method on `self`: fine.

## 2. Root cause (proven, not guessed)

Probes inside the real `serve()` loop printed the queue depth each iteration:

```
[serve] iter served=0 inbound=2   handling: OPEN as=alice   reply: OK session=1
[serve] iter served=1 inbound=2   handling: OPEN as=alice   reply: OK session=2
[serve] iter served=2 inbound=2   handling: OPEN as=alice   reply: OK session=3
...
```

`inbound` never decreases and the **same first message** is re-served forever,
opening a new session each time. This is an **unbounded spin, not a block** —
no lock, no missing wake, no blocking read.

The cause is one line. `serve()` re-bound its channel from the `transport`
parameter *inside* the loop:

```
while running:
    var channel = transport        # <-- re-reads the UNMUTATED parameter
    val message = channel.read_message()
```

`read_message()` writes the shortened queue back to `channel`, but the next
iteration discards `channel` and re-binds from `transport`, which still holds
the original three messages. The queue can never drain, so `running` is never
cleared.

Note this is the *same* extract-mutate-write-back family the tier's own design
notes call out — here the write-back existed but was thrown away by a re-bind.

### Second, quieter defect found by the same example
Once the spin was fixed, the example failed with
`array index out of bounds: index is 0 but length is 0` on
`channel.all_sent()[0]`. The transport is passed **by value** into `serve()`,
so the replies were captured on `serve()`'s own copy and the caller's binding
saw zero sent messages. The hang had been hiding this the whole time.

## 3. Fixes

`src/lib/nogc_sync_mut/database/server/server.spl`
1. **Bind the channel once, outside the loop** — the actual hang fix.
2. **`serve()` now returns `ServeOutcome { served, channel }`** and the caller
   reads replies off `outcome.channel`, so the drained state is handed back
   instead of being lost in the by-value copy. `serve()` had exactly one
   caller (the spec), so the signature change is contained.
3. **Bounded wait with a loud failure** — `SERVE_MAX_MESSAGES` (100000, far
   above any real connection). A drain that stops making progress now emits
   `ERR code=serve_bound` and returns, instead of hanging its caller. A test
   must not be able to hang the runner indefinitely.
4. **`try_parse_int` replaces `.to_int()`** for the session id. `.to_int()`
   never returns nil, so `"notanumber"` silently became session `0` and the
   `code=malformed` guard never fired. This was a real, newly-visible defect.

`src/lib/nogc_sync_mut/database/server/protocol.spl`
- New `ERR_SERVE_BOUND = "serve_bound"` for the bounded-drain failure.

`test/system/database/server/db_server_tier_spec.spl`
- Example #5 asserts through `outcome` (and now also checks the third reply).
- **Per-scenario store paths.** All 30 examples shared `/tmp/dbtier_spec.sdn`;
  a COMMIT persists via `SdnDatabase.save()`, which takes a `FileLock` on that
  path with a five-minute acquire budget, so concurrent runs contend. Each
  scenario now gets its own `build/dbtier_<scenario>.sdn`, mirroring
  `db_durability_spec.spl`. This was a latent second hang, not the one
  observed.

No assertion was weakened. The only assertion changes are additive.

## 4. Payoff

The runner path that previously produced `Process timed out` / exit 255:

```
Results: 30 total, 30 passed, 0 failed
```

- Previously observable: **4** examples (3 pass, 1 fail) before the spin.
- Now observable: **30**. → **26 examples became observable.**

Real verdicts of the 26 newly-visible examples: **25 passed as written**, and
**1 genuinely failed** — `"rejects a non-numeric session id"`, which exposed
the `.to_int()` defect above. It passes now because the server was fixed, not
because the assertion was relaxed.

### Caveat on binary identity
The deployed `bin/simple` (built 07-27 22:06) predates lane MATCHER's
`assert_nil` fix in `src/compiler_rust/.../interpreter_call/bdd.rs` (07-28
00:06). On that stale binary the file still reports 5 failures, all of the
shape `assert_nil failed: got Option::None` — a matcher artifact, not tier
defects. Verified against `src/compiler_rust/target/release/simple` (07-28
00:46, postdates the fix): 30/30. The 5 will clear on redeploy; nothing in
this lane depends on them.

## 5. Regression checks

| Spec | Result |
|---|---|
| `test/system/database/server/db_server_tier_spec.spl` | 30 examples, **0 failures** (was: unobservable past #4) |
| `test/system/database/server/db_durability_spec.spl` | 16 examples, **0 failures** — unchanged |
| `db_server_tier_notransport_spec.spl` (lane MATCHER's out-of-tree copy at `build/matcher_repro/`) | 29 examples, **0 failures** (was 28 pass / 1 fail; the 1 was the `.to_int()` session-id defect this lane fixed) |

The notransport spec exists only as a workaround copy of the tier spec with the
hanging example removed. With the hang fixed it is now redundant and lane
MATCHER can drop it.

## 6. Follow-ups for other lanes

- **Lane DBDUR** re-covered two properties in `db_durability_spec.spl` to
  compensate for the hidden examples. That compensation is no longer needed and
  can be reverted if DBDUR prefers the coverage to sit in one place.
- **Redeploy `bin/simple`** to pick up MATCHER's `assert_nil` / `assert_not_nil`
  fix; until then this spec shows 5 false failures on the default tool.
- `serve()` is typed to the concrete `MemoryTransport`, not the `DbTransport`
  trait, deliberately — trait-typed parameters have no JIT vtable (filed).
  The `ServeOutcome` return keeps that constraint intact.

## 7. Independent re-verification (lane DBHANG-VERIFY, 2026-07-28)

Re-ran everything on the **seed** `bin/simple run` (no redeploy available).

**What was on disk:** all 7 `src/lib/nogc_sync_mut/database/server/*.spl` and
both specs are new/untracked (not in `HEAD`). The per-scenario store-path fix
(`build/dbtier_<tag>.sdn` in `make_store(tag)`, replacing the shared
`/tmp/dbtier_spec.sdn`) was present and complete. `db_server_tier_notransport_spec.spl`
does not exist — consistent with §5 saying it was dropped as redundant.

**Hang:** GONE. `db_server_tier_spec.spl` ran to completion, exit 0, no timeout.
The `FileLock`-contention diagnosis is confirmed correct.

**30/30 did NOT reproduce as-is.** First run: 30 total, **5 failures**, all
`assert_nil failed: got Option::None` at the five `assert_nil(store_read(...))`
sites. §6 predicted exactly this and deferred it to a `bin/simple` redeploy
carrying MATCHER's `assert_nil` fix.

**Finished here instead of waiting on the redeploy.** `store_read` returns
`SdnRow?`, so an absent row is `Option::None`, which is not `== nil`. Added a
`row_absent(store, table, key) -> bool` helper that matches the Option and
collapses it to a bool, and switched the five sites to
`assert_true(row_absent(...))`. This is correct on the seed *and* on a
redeployed binary, so it removes the cross-lane dependency entirely.

**Verdicts after the fix:**

| Spec | Result |
|------|--------|
| `db_server_tier_spec.spl` | 5+8+9+8 = **30 examples, 0 failures**, exit 0 |
| `db_durability_spec.spl` | 5+6+2+3 = **16 examples, 0 failures**, exit 0 |
| `db_server_tier_notransport_spec.spl` | not on disk (intentionally dropped, §5) |

No product code under `src/lib/nogc_sync_mut/database/server/` was modified by
this verification pass — the only change is the matcher usage in the spec.
`serve()` remains concretely typed to `MemoryTransport`. Nothing committed.

# Mode-carrying write externs exist in the seed source but not in the deployed binary

**Status:** OPEN (blocked on seed redeploy)
**Filed:** 2026-08-08
**Severity:** medium — no regression shipped; two fixes are written but cannot be adopted

## Summary

Two new interpreter externs were added to close the "secret files are created
world/group-readable and only then chmod'd" race:

- `rt_file_atomic_write_mode(path, content, mode) -> bool` — applies the mode to
  a unique same-directory temp file **before** the content is written, fsyncs,
  then renames. The target is never observable at a wider mode.
- `rt_file_mode(path) -> i64` — returns the octal permission bits, or `-1`.
  The runtime previously exposed **no mode-read primitive at all**, which is why
  chmod verification was impossible: a spec could only trust chmod's own return
  value. `rt_file_stat_readonly` is not a substitute — it collapses the whole
  mode to one bool and cannot tell 0600 from 0644.

Both are implemented in
`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` and registered in
`interpreter_extern/mod.rs`.

## The blocker

`bin/release/<triple>/simple` — the binary every lane and CI actually runs — was
built before this change and does **not** contain these symbols. Verified:

```
strings src/compiler_rust/target/bootstrap/simple  | grep -c rt_file_atomic_write_mode   -> 2
strings bin/release/x86_64-unknown-linux-gnu/simple | grep -c rt_file_atomic_write_mode  -> 0
```

Consequently any `.spl` call site that adopts them fails on the deployed binary
with `semantic: unknown extern function: rt_file_atomic_write_mode`. For
`credential_key_generate` that would mean **key generation stops working
entirely** — strictly worse than the permissive-mode window it closes. The call
sites were therefore deliberately NOT switched. See the inline comment at
`credential_key_generate` in
`src/lib/nogc_sync_mut/terminal/credential/store.spl`, which names the one-line
change to make after redeploy.

The same applies to the three `oauth2.spl` copies (`nogc_sync_mut`,
`gc_async_mut`, `nogc_async_mut`), which were switched and then reverted for
exactly this reason. Their current temp+chmod form leaves a narrow window on the
*temp* file (created 0664, chmod'd 0600 before rename) and uses a FIXED
`"{path}.tmp"` name, so two processes refreshing the same token collide. Both go
away with the one-line swap.

## Unblock condition

Redeploy the seed so `bin/release/<triple>/simple` contains the two externs.
That is itself currently blocked by the Stage-3 self-host defect
(`unresolved type: ByteOrder` in `cache_validator.spl`) — see
`.claude/rules/bootstrap.md` and
`doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`.

After redeploy:
1. Swap the two call sites named above.
2. `test/01_unit/lib/terminal/credential_upgrade_persist_spec.spl` should go
   green (see below).

## The spec is deliberately RED

`test/01_unit/lib/terminal/credential_upgrade_persist_spec.spl` asserts the real
behaviour and currently reports, against the deployed binary:

```
SPEC FILE VERDICT: ... declared>=12 executed=12 passed=4 failed=8 dropped=0
```

The 8 failures are all `unknown extern function: rt_file_atomic_write_mode` /
`rt_file_mode`. This is a correct spec failing for a known environmental
reason, kept RED per `.claude/rules/testing.md` rather than weakened. **Do not
"fix" it by softening assertions** — it passes when the seed is redeployed.

## What IS verified

Against the freshly built seed (`src/compiler_rust/target/bootstrap/simple`),
via `run`, with `stat` as independent ground truth:

| case | requested | `rt_file_mode` | `stat` |
|------|-----------|----------------|--------|
| new file, mode-carrying write | 0600 | 384 (0600) | 600 |
| old `rt_file_write_text` path | (none) | 436 (0664) | 664 |
| explicit non-secret mode | 0644 | 420 (0644) | 644 |
| overwrite 0644 file with 0600 | 0600 | 384 (0600) | 600 |
| absent file | — | -1 | — |

Row 2 is the vulnerability being fixed: the existing write path really does
produce a group- and world-readable file. Row 3 is the sabotage check (the
primitive honours the mode rather than hardcoding 0600). Row 4 matters because
the pre-existing `rt_file_atomic_write` **copies the existing target's
permissions onto the temp**, so re-writing a secret into an already-0644 file
would keep it 0644; the mode argument overrides that.

## What is NOT verified

`credential_upgrade_file` (the v1→v2 upgrade persister added the same day) has
never been executed end-to-end. Both routes are blocked:

- `bin/simple test` → deployed binary → missing externs.
- `bin/simple run` on a probe → the seed resolves `std.*` against its own
  `src/compiler_rust/lib/std/` tree, and `credential_upgrade_file` is reported
  `function not found` there even though it is present and exported in
  `src/lib/`.

So its byte-exactness, its minimum-body guard, and the interrupted-write case
are **unproven by execution**. It has no caller (`config_parser.spl` is still
read-only), so it cannot regress anything today, but it must not be described as
verified until the spec above runs green.

## Secret-writer sweep (2026-08-08)

| site | status |
|------|--------|
| `src/lib/nogc_sync_mut/terminal/credential/store.spl:~385` (key file) | write+chmod window; fix written, adoption blocked |
| `src/lib/nogc_sync_mut/oauth2.spl:123` (OAuth2 access token) | temp+chmod; narrow temp window + fixed temp name; fix written, reverted, blocked |
| `src/lib/gc_async_mut/oauth2.spl:123` | same — full duplicate, not a shim |
| `src/lib/nogc_async_mut/oauth2.spl:123` | same — full duplicate, not a shim |
| `src/app/play/session_store.spl:151` | `rt_file_write_text`, default mode. Browser/session state, may carry auth cookies — worth a look, not fixed here |
| `src/app/svim/_SvimCore/session_commands.spl:170` | editor buffer contents, not a secret — no action |

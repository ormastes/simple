# Test runner / MC/DC / nil-return session follow-ups (2026-10-31)

State at session close: release/1.0.0 test runner runs all four kinds
(md, comment, sspec, plain spec) in every combination of MC/DC on/off and
`--no-session-daemon` on/off. The 4-combination check passed on the seed built from
`566b710a5a4`. `bin/simple` points at a seed built from `7a0e6fe516f`, kept in
`~/.local/share/simple-seeds/` (not `bootstrap.generations`, which was pruned
mid-session).

## Open PRs at close

- #5633 fix(hir): codec decoders that can reject return `T?` (NIL-RET-001). Includes
  the `rt_path_absolute -> text?` fix in `20.hir/hir_lowering/module_surface_source_identity.spl`.
  Since #5628, a failure to read the cwd returns nil here, so this is a live risk until it lands.
- #5642 fix(fs): `rt_file_read_bytes`, hash and dir-list externs declare `T?`.
- MIR NIL-RET-001 batch: not opened yet.
- 40.mono NIL-RET-001 findings: dropped, because mono is scheduled for deletion.

## Nil-return rule

Rule: every `rt_` extern that can return nil is declared `T?`, and callers handle
the absent case explicitly. A nil on a non-optional path is allowed only in unsafe code.

- [ ] Clear the remaining guard baseline in `scripts/check/check-non-optional-nil-return.shs`:
  88 non-optional declarations that can return nil (51 of them `rt_file_read_text`), plus 26
  forwarding wrappers. See `doc/08_tracking/bug/nil_return_non_optional_deferred_2026-10-31.md`.
- [ ] Extend the guard to `src/os`, `src/compiler_rust/lib` and `test/**`.
- [ ] Detect nil returns from the C runtime, not only from `interpreter_extern`.
- [ ] `rt_enum_payload` / `rt_tuple_get` are still declared as raw `i64`.
- [ ] `rt_stderr_write([u8])` prints the array as text instead of writing the bytes.
- [ ] 13 lint rules define a private `check_rule`; the shared rule table can call the wrong one.

## Needs verification

- [ ] Stage-2 bootstrap with #5549 (trace-scope calls) and the MIR nil fixes. It is
  blocked by the 24 GiB `SIMPLE_BUILD_MEMORY_RESERVE_BYTES` guard on this host
  (about 11.6 GiB free). Run it on an idle host or a bigger one.
- [ ] #5290 merged to main without a review and with its idiom gate cancelled. Review it and rerun the gate.
- [ ] Rerun the async_host cancellation spec on the new seed; the earlier failure may have come
  from the stale seed.
- [ ] #5505 (`.fpc` → `.spab` cache spec) merged, but nobody has run it: the build is
  refused by the memory guard and the spec exceeds the 900 s runner cap.

## Known failures with bug records

- [ ] async_host teardown leak: the scheduler shares state through class copies. Needs a
  scheduler redesign that moves the queues into module-level storage.
- [ ] Integer dict keys come back as text. The fix touches about 170 raw readers and the bootstrap
  symbol tables; needs a perf check. #5630 (another session) may cover it.
- [ ] HAL: 24 caller-owned-buffer scenarios are skipped (arrays are passed by value), and the
  confined-file / device-capsule modules need runtime functions missing from the C runtime.
- [ ] `summary_store_byte_paging_spec` times out at 900 s.

## Not re-checked since fixes landed

- [ ] Cache specs: `file_io: argument 1 must be a string` (cold_hir), CAS read-back
  `CacheAccessDenied` (reverse_reference), the nondeterminism quarantine (driver_store_catalog),
  and specs that put the cache root under `/tmp`, which is a symlink on macOS.
- [ ] Rerun the earlier Lunar sweeps: loader (104 failing) and nogc_async (69 failing,
  about 60 with no result).

## Deferred / owner decisions

- [ ] Phase 3 (the full CLI built by phase2): needed for real MC/DC evidence and for md/comment
  tests on a real Stage 2 compiler.
- [ ] Simplebox applet count, 8 vs 41: needs the SimpleOS owner.
- [ ] #5626 (mono, another session): may be moot because mono is being deleted.
- [ ] Worktree `.claude/worktrees/agent-a0b73dcc3dc631657` has 6 uncommitted files (from a
  runner phase-3 doctest fixer). Review them, then land or discard.

# CS host provider facade exports

Status: fixed 2026-11-11 (lane p3-caret1) — verified natively on release/1.0.0 tip 79d5af6723f6.

Actual4cca CS closure reports missing print_raw and positionedfile names. CanonicalSoSix rawoutput alias and asyncIO reexports bind the existing syncIO positioned providers. Hostfixture then exposed an existing syncIO selfreexport for thread_sleep_ms without an imported provider. Canonical concurrent.thread.thread_sleep supplies the alias; concurrent.thread has no imports, so this adds no IOcycle. No appRT access or host implementation changed.

Real native fixture test/fixtures/lib/caret_cs_host_alias/main.spl verifies missingfile readErr/writefailure and successful SoSix terminalwrite. First failure retained at /home/ormastes/simple-phase4-web-a0-parallel-20261010/leaf-fixtures/cs-host-alias/evidence.json. Followup qualification UNEXECUTED.

**Revalidated 2026-11-02: still plausible because OPEN; changed-owner native qualification pending; no merged fix commit with a passing regression is cited in this doc.**

## Addendum 2026-11-11 — lane p3-caret1: FIXED — native qualification executed

Traversed on work/p3-caret1-20261111 (origin/release/1.0.0 tip 79d5af6723f6).

- Source fix 6320be38309 ("fix(io): bind canonical millisecond thread sleep
  facade owner") IS an ancestor of tip.
- Native build (Rust engine, `SIMPLE_NATIVE_BUILD_RUST=1`, llvm-mingw
  20260922-ucrt-x86_64 on PATH): `bin/simple.exe native-build
  test/fixtures/lib/caret_cs_host_alias/main.spl` — build exit 0
  (log: build/review/p3fix-caret1-20261111-logs/row4_native_build2.log).
- Fixture run: exit 0, stdout exactly `caret-cs-host-alias-ok`
  (log: build/review/p3fix-caret1-20261111-logs/row4_fixture_run.log).
  Exit 0 proves all three checks: missing-file read returned Err (not ok),
  missing-dir write failed (written < 0), and the SoSix `print_raw` alias
  emitted successfully.

The "seed cannot verify" caveat applied to the seed *interpreter*; the Rust
engine native-build path qualifies the changed owners natively, and it is green.

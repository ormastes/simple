# `push-main-test-runnable` cannot pass on this host — no deployed binary both has `test` and reads the tree (2026-09-03)

Status: RESOLVED — re-verified on macOS aarch64 at `origin/main@b9667d6584f`,
2026-09-12. The gate no longer requires a full-CLI binary that both has `test`
and reads the tree; `b623eef45f5` rebuilt it as a `--rev` guard over the
COMMITTED tree's startup-path `.spl` parse, which is a property of the commit
rather than of the host's deployed artifacts. That dissolves the
unsatisfiability recorded below — the four-row table of "no binary on this host
satisfies C2" no longer describes what the gate asks for.

Measured on this Mac, with a FRESH marker directory so the content-keyed green
fast path cannot launder the verdict (the first run hit the fast path and said
`1 fixture invocation skipped`; this one did not):

```
$ MAIN_RUNNABLE_MARKER_DIR=<fresh empty dir> \
    sh scripts/check/check-main-test-runnable-push.shs ; echo rc=$?
check-main-test-runnable-push.shs: PASS — 1 fixture invocation executed at
  b9667d6584f87f09abc8774f9a404c0961ffc2b0, tree is test-runnable
  (startup-path content 69918c864c54ff8c9d6f05c5bdee0f16 recorded green)
rc=0
```

`1 fixture invocation executed` (not `skipped`) is the non-vacuity evidence.
Note this worktree has **no `bin/simple` at all** — the gate passes anyway,
which is the point: it is no longer coupled to a deployed binary. The
`/mnt/data` hardcode this record's lane also covered is already portable at
`:90-95` (`_main_runnable_scratch_base` falls back to
`$SIMPLE_USER_STORAGE_ROOT`), so no edit was needed there either.

The `run_fixture_in` self-clobbering ELOOP defect recorded in the 2026-09-04
update below is likewise gone with the rewrite.

## Verdict

```
SELFTEST FAIL: C2 — an unparseable env_access_host.spl still ran green;
               the binary is not reading the tree under test
check-main-test-runnable-push.shs: FAIL — selftest failed; no scan was run
push-must-check: BLOCKING gate push-main-test-runnable failed (exit 1)
```

The C2 selftest injects a syntax error into a fixture and requires the binary to
fail with a PARSE diagnostic. It is a good check: it is the only thing that
notices a binary which *looks* healthy while serving a baked-in stdlib or cached
artifacts instead of the working tree.

## Measured across every binary available here

| `bin/simple` resolves to | `--version` | C2 result |
|---|---|---|
| (absent — guard's own fallback) | — | `fail:rc=1: error: unknown command 'test'` → FAIL |
| `bin/release/aarch64-apple-darwin-macho/simple` | `simple-bootstrap 1.0.0-beta` | `unknown command 'test'` → FAIL |
| `bin/release/macos-arm64/simple` | `Simple v1.0.0-rc.1` | ran GREEN on unparseable source → FAIL |
| `bin/release/aarch64-apple-darwin/simple` | `Simple v1.0.0-beta` | ran GREEN on unparseable source → FAIL |

So: the binary that reads the tree has no `test` subcommand, and the two that
have `test` do not read the tree. There is no configuration on this host that
satisfies the gate.

This is the condition CLAUDE.md already records — no FULL-CLI pure-Simple binary
is deployed — surfacing as a hard blocking gate rather than a footnote. Note
`bin/simple` currently points at the BOOTSTRAP build
(`aarch64-apple-darwin-macho`), which is also why `bin/simple lint` answers
`unknown command 'lint'`.

## Why it appeared only today

`push-sffi-v2-authority` precedes it in the manifest and had been failing first
for macOS-only tooling reasons (BSD `wc` padding; `nm` on a shell-wrapper
`bin/simple`). With those fixed, execution reaches this gate for the first time.
It was always red here; nothing regressed.

## Not caused by any branch

The gate exercises a fixture and the deployed binary. It does not read the
pushed range.

## Resolution

Redeploy a full-CLI pure-Simple binary that reads the working tree (bootstrap).
Until then every push from this host must bypass this gate; there is no scoped
override (the selftest is fatal by design, and both `SIMPLE_BIN` and
`MAIN_RUNNABLE_MARKER_DIR` only change WHICH binary is probed, not the C2
requirement).

## Verified state of the other gates (same tree, same run)

With no local `bin/simple` and `SFFI_MAX_SOURCE_SIGNATURE_VARIANTS=416` stated:

```
sffi-v2-authority: PASS — all 46 guard(s) passed          (SFFI_RC=0)
check-main-test-runnable-push.shs: FAIL                    (MTR_RC=1)
```

and from the push run itself: conflict-tree PASS, tree-size PASS
(`--expect-files 133451`), conflict-markers PASS, runtime-api-regression PASS
(2947 symbols, 0 removed), c-runtime-compiles PASS (125 files, 0 errors),
no-direct-rt PASS (16,238 files), guard-wiring PASS (1539 guards, 0 new unwired,
0 copied hooks), type-walk-constructor-parity PASS (12 constructors),
windows-checkout-damage PASS (1212 paths, 0 damage).

## Update 2026-09-04 — the guard also DESTROYED the deployed CLI on every run

Separate from the unsatisfiability above, `run_fixture_in` provisioned the
child-compiler path unconditionally:

```sh
ln -sf "$(readlink -f "$_bin")" "$_dir/bin/simple"
```

When the tree under test is the repo itself and `bin/simple` is a regular-file
exec wrapper (which it is on this mac — the stage4 binary resolves its stdlib
from `argv[0]`, so a plain symlink cannot be used), `readlink -f "$_bin"` is
that same path, so the link pointed `bin/simple` at itself. Every later exec
then failed with `ELOOP` — `timeout: failed to run command
'.../bin/simple': Too many levels of symbolic links` — and the selftest
reported the damage it had just caused as fixture C2 failing "not with a parse
diagnostic". The deployed CLI stayed broken after the push aborted.

Fixed by comparing resolved paths and relinking only on a genuine mismatch.
After the fix, fixture F passes and C2 reduces to the real, documented cause:
`error: unknown command 'test'` — the deployed binary is the BOOTSTRAP CLI
(`simple-bootstrap 1.0.0-beta`), which exposes only `compile` and
`native-build`. That is the unsatisfiability recorded above, unchanged.

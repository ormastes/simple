# `push-main-test-runnable` cannot pass on this host — no deployed binary both has `test` and reads the tree (2026-09-03)

Status: OPEN — environmental, blocks every push from this machine

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

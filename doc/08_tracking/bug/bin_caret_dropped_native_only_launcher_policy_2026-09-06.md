# `bin/caret` dropped its native-only launcher policy

Date: 2026-09-06
Status: OPEN — deliberately NOT fixed (see Decision)
Area: `bin/caret`, `bin/cs`

## Summary

`bin/caret` no longer implements the launcher policy its own committed spec
requires. `test/01_unit/app/llm_caret/messaging/caret_launcher_policy_spec.spl`
fails **2 of 3** examples:

```
3 examples, 2 failures
SPEC FILE VERDICT: ... outcome=ERROR declared>=3 executed=3 passed=1 failed=2
```

## What the spec requires vs. what `bin/caret` does

The spec asserts `bin/caret` contains:

| required token | present today |
|---|---|
| `messaging_supervisor=1` | NO |
| `"Interpreting this control plane therefore never"` | NO |
| `"interprets the PureDatabase hot path"` | NO |
| `src/app/llm_caret/messaging/main.spl` | NO |
| `SIMPLE_CARET_ALLOW_SOURCE_FALLBACK:-0` | NO |
| `"cached native Caret artifact not found"` | NO |

The third example — which asserts on `src/app/llm_caret/messaging/main.spl`
itself — still passes, and that file still exists (455 bytes). So the spec is
**live policy, not a stale artifact of a removed design.**

Today `bin/caret` is a plain runtime probe that unconditionally does:

```sh
exec "${runtime}" run "${REPO_ROOT}/${CARET_ENTRY:-src/app/llm_caret/main.spl}" "$@"
```

i.e. it interprets ~11K LOC of caret from source every run, with no native
preference and no fallback gate.

## When it regressed

`git log -- bin/caret` shows the file was last rewritten by
`4af3725d9cc feat(caret,mcp): cs caret suite, code-burn report, toolchain log-opt plugins`.
That commit introduced the `CARET_ENTRY` indirection so `bin/cs` could reuse the
runtime probe, and in doing so replaced the whole wrapper, silently discarding
the native-only policy. `git log -S'SIMPLE_CARET_ALLOW_SOURCE_FALLBACK'` confirms
the token is absent from the current file.

## Decision (2026-09-06): file, do not fix

Restoring the policy was considered and explicitly declined by the repo owner
this session, because on this host it would break both working entry points:

- No cached native `caret` artifact can be produced here. The documented
  producer (`doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md` § Cached Caret
  Artifact and Provenance Contract) requires a self-hosted
  `bin/release/<target>/simple` that is **not** the Rust seed, and refuses on a
  binary whose `--version` says `bootstrap seed only` — which is exactly what
  `bin/release/aarch64-unknown-linux-gnu/simple` says. No `simple_seed` delegate
  exists either.
- With the policy restored and no artifact present, `bin/caret` **and** `bin/cs`
  (which execs `bin/caret` via `CARET_ENTRY`) would both refuse to start unless
  `SIMPLE_CARET_ALLOW_SOURCE_FALLBACK=1` were exported for every invocation.

Trading two working tools for a green spec was judged the wrong call while the
bootstrap that would supply the artifact is itself blocked.

## Unblock condition

Restore the policy once a genuine self-hosted `bin/release/<target>/simple` is
deployed and the cached `caret` artifact can actually be built. At that point the
three artifact-dependent gates
(`check-llm-caret-cli-cached.shs`, `check-llm-caret-cli-hidden-cached.shs`,
`check-llm-caret-tui-pty.shs`) also stop reporting
`cached_caret_artifact_missing` and become real smoke coverage — they are
currently, and correctly, fail-closed on the same unmet precondition.

Do not "fix" this spec by weakening or skipping it.

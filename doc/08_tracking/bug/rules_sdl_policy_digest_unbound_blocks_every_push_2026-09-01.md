# rules.sdl policy digest unbound — `push-rules-quick` ERRORed on every push

- **Filed:** 2026-09-01
- **Severity:** critical (repo-wide: every push bypassed all 19 push gates)
- **Status:** fixed by this change

## Symptom

On unmodified `origin/main` (`d53955eb752`), in a clean worktree:

```
sh scripts/check/check-rules-sdl.shs --scan-only --group quick --ref origin/main
rc=2
ERROR — nothing was checked (committed rules.sdl is not bound to the reviewed policy digest)
```

`push-rules-quick` is a BLOCKING `push` row in `config/check/must_check_gates.sdn`,
so the pre-push hook ended `BLOCKING gate push-rules-quick failed (exit 2)` for
EVERY push. The practical consequence: every push in this repo was being made
with `--no-verify`, which skips all 19 push gates — including the ones just
wired by PRs #278 and #280. A guard everyone routes around protects nothing; this
one was disabling the entire fence.

## Mechanism

`scripts/check/check-rules-sdl.shs` pins the reviewed policy content by SHA-256:

- `RULES_POLICY_SHA256=028c10460522549495d9142b90d5512dd5dcf79657f2fa9f3d72ca7b50442dfd` (line 25)
- `rules_policy_matches()` (line 71) `sha256sum`s the COMMITTED `rules.sdl`
  (materialised via `git show "$REF:rules.sdl"`) and compares.
- On mismatch, line 204 emits the ERROR above and exits 2 — deliberately
  fail-closed, so `rules.sdl` cannot change without a reviewed digest update.

The guard behaved correctly. The **content** was wrong:

| commit | rules.sdl sha256 |
|---|---|
| `86d39fbe8d2` | `498c19ada7be…` |
| `a369b5578bc` | `6deb62568455…` |
| `e2af40d1b5c` | **`028c104605…`** ← the blessed, reviewed content |
| `f1918d87e6b` "feat: snapshot current development state" | `6deb62568455…` ← **reverted to a369's content** |
| `origin/main` tip | `6deb62568455…` |

`f1918d87e6b` is a stale whole-working-copy snapshot — precisely the anti-revert
failure mode `.claude/rules/vcs.md` § "Sync must never clobber" describes. It
rewound `rules.sdl` past `e2af40d1b5c`. `git log e2af40d1b5c..origin/main -- rules.sdl`
lists only that one commit, so nothing else depends on the clobbered content.

The entire delta it reverted is **two comment lines** — and, with grim irony,
exactly the two that document the digest binding:

```
# Production evaluation is also SHA-256 bound in check-rules-sdl.shs; review
# and update that binding whenever this registry intentionally changes.
```

**Zero gate rows differ.** No policy change was involved, in either direction.

## Fix

Restore `rules.sdl` to the already-reviewed `e2af40d1b5c` content, byte for byte
(`git show e2af40d1b5c:rules.sdl > rules.sdl`; verified `sha256sum` ==
`028c1046…`). The guard, the pinned digest, and the blocking gate row are all
left untouched.

Deliberately NOT done: blessing the clobbered content with a fresh digest. That
would have laundered a stale-snapshot revert into reviewed policy. The blessed
version is a strict superset of the tip version, so restoring loses nothing.

## Recurrence

The clobber landed because a whole-WC snapshot commit was pushed over a file the
session had not authored — the exact hazard vcs.md § "Sync must never clobber"
rule 2 forbids. The revert-detection half of that protocol is still manual and
still unimplemented as a guard; this incident is a second concrete argument for
building it.

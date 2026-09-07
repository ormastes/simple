# verification Layer Expert

## Role

Maintain process knowledge for the `verification` layer: owned source, architecture links, expected tests, and boundary rules. Use this skill when a task changes `src/verification` or depends on its public behavior.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Layer Links

- [Source](../../../src/verification/)
- [Architecture index](../../04_architecture/README.md)
- [Architecture modules](../../04_architecture/architecture_modules.md)
- [Design docs](../../05_design/)
- [Generated spec manuals](../../06_spec/) mirrored from executable
  `test/**/*_spec.spl` files; executable specs must stay under `test/`.

## Update Rule

When project work changes this layer's public contract, source ownership, tests, architecture, or verification requirements, update this skill with current links and handoff notes.

Template: [layer_skill.md](../../template/layer_skill.md)

## Handoff — local CI receipt gates (2026-09-06)

Scope note: this section covers gate/verification TOOLING under
`scripts/check/` and its CI consumers, not `src/verification`. It is recorded
here because that tooling is where this layer's verification requirements are
actually enforced.

Two new guards, both following the repo guard contract (verdict line LAST on
stdout, `PASS — <n> ... ` / `FAIL — ...` / `ERROR — nothing was checked (...)`,
exits 0/1/2, non-vacuity absolute so 0 items is ERROR, and a fatal `--selftest`
that runs before every scan):

- `scripts/check/sign-local-ci-receipt.shs` — mints and sshsig-signs a receipt
  (`simple.local-ci-receipt/v1`). It records verdicts FAITHFULLY and is not the
  gate: it will sign a receipt containing a non-pass row and exit 1. A signer
  that refused to record a failure would turn "the gates failed" into "no
  receipt exists", which is a weaker statement.
- `scripts/check/verify-local-ci-receipt.shs` — the thing that decides
  admissibility. Fails closed on missing receipt, missing signature, absent or
  pre-8.0 OpenSSH, symlinked inputs, non-canonical payload, tamper, unknown
  signer, an unbindable commit (no change-id header AND no patch-id — a merge or
  an empty diff), an identity KIND mismatch, an identity-set or tree mismatch,
  manifest mismatch, id-set drift, or any row not `pass`. It resolves BOTH
  identity kinds, `change` and `patch`, and the kind is part of the signed bytes,
  so a `patch` identity never satisfies a `change` one.

Idioms to preserve when touching either: exit status read DIRECTLY into a
variable on the line after the command, never through a pipe; the payload's
exact bytes are fed to `ssh-keygen -Y verify` and are never re-serialized before
verification (a one-newline drift looks identical to an attack); the manifest is
read as `git show <tree>:config/check/must_check_gates.sdn`, never from the
working tree, because "as of that tree" is the binding and a working-tree read is
fail-open under a dirty checkout; `ssh-keygen -Y verify` exits **255** on tamper,
not 1, and a fixture pins that.

CI consumer: the `code-idiom-gates` job of `.github/workflows/repo-hygiene.yml`.
FOUR modes — `docs`, `sanity`, `escalate`, `full` (the workflow's own header
comment still says "THREE MODES, and only three"; it is stale, read the code) —
and the fail-closed hinge is
the INVERTED per-step `if:` (`!contains(steps.receipt.outputs.skip_ids,
'|<row id>|')`). An empty, missing or unset `skip_ids` makes `contains` false, so
the gate RUNS; a decision step that dies or emits nothing runs everything. Never
replace that with a positive condition or a `needs:`/`if:` job gate — the
obvious positive form is fail-OPEN, and a skipped job reports as passing.
The conflict-class guards (conflict-tree, conflict-markers, tree-size) are
BLOCKING in every mode, gated only on `range != ''`; in `sanity` and `docs` they
are the only enforcement left. Measured 8 s total on a CI-shaped range, so they
fit the 60 s budget. They have not yet run on a CI runner — neither has any
other part of this path.

Reading order for a task in this area:
`doc/07_guide/infra/local_ci_receipt/operator_guide.md` (task-oriented, with the
verdict-string troubleshooting table and both open gaps),
`doc/05_design/infra/local_ci_receipt/design.md` (specification),
`doc/03_plan/infra/local_ci_receipt/plan.md` (acceptance bars),
`doc/00_llm_process/feature_expert/must_check_tiering/skill.md` (the manifest
and ledger this extends).

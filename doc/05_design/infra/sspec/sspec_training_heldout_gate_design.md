# SSpec Training Held-Out Gate — Design

**Date:** 2026-09-05 · **State:** `.spipe/sspec_training_heldout_gate/state.md` · **Plan:** `doc/03_plan/infra/sspec/sspec_training_heldout_gate_plan.md`
**Research:** `doc/01_research/infra/spipe/spipe_skill_foundry_debug_dump_replay_v2_2026-09-05.md` §14 (episodes), §18 (anti-cheat)

## Decision

The training loop is `checklist → low-effort worker → spec → scorer → histogram → checklist edit`. It
works — same haiku, same files: 84/78/78 under the old checklist, 90/90/90 under the new — but the loop
has the "wrong flywheel" shape the foundry design warns about: a checklist tuned until known files pass
measures the checklist's memory of those files, not transfer. The repo already admits the honest number is
14/14 held-out, not 21/21, and names three missing controls. This design adds exactly those three and
nothing from foundry Waves 2–5.

The partition is DATA (`.spipe/training/splits.sdn`), the gate is the existing scorer wrapper
(`sspec-train.shs --split`), and the leak rule is mechanical: the held-out set is void if the checklist
is no longer byte-identical to the one it was frozen against, or if the checklist text cites a held-out
spec. Both conditions ERROR the whole run — a partially-leaked held-out set is not a smaller held-out
set, it is no evidence.

Direction matters, and the first draft got it backwards: in this loop the worker is *supposed* to edit
the held-out spec after the checklist freeze — that is the training step — so "spec modified after
cutoff" fires on every legitimate run (measured: all 14). The leak is the reverse edge, checklist edited
after seeing the spec, and its mechanical form is digest equality on the checklist file.

Field names are the foundry's verbatim (`split`, `source_case_uid`) so the file can be consumed by the
`Spipe` engine later without a rename; nothing else from `TrainingEpisodeV1` is carried because nothing
here reads it.

<!-- sdn-diagram:id=sspec_training_heldout_gate.design -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sspec_training_heldout_gate.design hash=sha256:auto render=ascii
@layout dag
@direction TB

Operator -> TrainScript
TrainScript -> SplitsSdn
TrainScript -> GitLog
TrainScript -> ChecklistText
GitLog -> LeakGate
ChecklistText -> LeakGate
SplitsSdn -> LeakGate
LeakGate -> Scorer
Scorer -> Verdict
```

</details>
<!-- sdn-diagram:end -->

## Interfaces

| surface | contract |
|---|---|
| `.spipe/training/splits.sdn` | header `schema: sspec-training-splits/v1`, `checklist_digest: sha256:<64 hex>` (of the checklist file at freeze); rows `source_case_uid` (spec path), `split` ∈ `train\|development\|private_test\|safety_test` |
| `sh scripts/check/sspec-train.shs --split <name>` | scores rows with `split == name`; last stdout line `PASS — <n> checked, split=<name>, target=<score>` / `FAIL — …` / `ERROR — nothing was checked (<reason>)`; exit 0/1/2 |
| leak gate A | sha256(checklist file now) ≠ `checklist_digest` ⇒ ERROR "checklist changed since freeze; re-partition" |
| leak gate B | `<path>` substring of `.spipe/spipe/doc/00_llm_process/spipe/skill.md` ⇒ ERROR |
| `--selftest` | +3 fixtures (digest drift, citation leak, clean split); fatal before any real run |

What gate A proves: the checklist is byte-identical to the frozen one. What it does not prove: that the
14 were unseen when that checklist was written — that rests on the recorded 13:50 (checklist) / 14:00
(first held-out edit) commit-timestamp argument in `modern_sspec/skill.md`, not on this gate.

## Non-goals
Graders, `SolverRunV1`, attribution, knowledge GC, provider execution — engine side (`Spipe/src/training`).

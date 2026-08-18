# bootstrap planner-admission-v2 is circular, and its receipt cannot express an imported parent

- **Date:** 2026-08-18
- **Status:** OPEN
- **Area:** bootstrap / admission gate

## 1. The admission cycle is closed on a fresh tree

`scripts/bootstrap/bootstrap-from-scratch.sh:301` refuses to start without a
planner-admission-v2 receipt (exit 64, `reason-receipt-required`). The only
producer, `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`,
requires a parent compiler under `$root/build/bootstrap/stage2/` carrying
`stage2-sanity.receipt` and `stage2-provenance.receipt`
(producer lines 83-96). On a tree with no `build/bootstrap/stage2/` this fails
`parent-compiler-missing-or-not-canonical`.

So: receipt needs stage2, stage2 needs a bootstrap run, the bootstrap run needs
the receipt. A tree that has never bootstrapped cannot bootstrap.

## 2. Nothing in the repo ever WRITES the two receipts the gate reads

`/usr/bin/grep -rn 'stage2-provenance' scripts/` returns exactly two producers
of the file: the producer script that READS it, and
`scripts/check/check-bootstrap-planner-admission-producer.shs`, which writes it
only inside its own throwaway selftest fixture. `bootstrap-from-scratch.sh`
writes `stage2-sanity.env` (a different filename and schema) but never
`stage2-sanity.receipt` or `stage2-provenance.receipt`.

The gate therefore depends on two files that only a human hand-writes. That is
the mechanical reason the cycle above has no legitimate exit.

## 3. The receipt schema cannot record that the parent was imported

The v2 receipt's 29 keys are pinned by
`scripts/check/lib/bootstrap-planner-admission-bound.shs:74`. It records
`parent_compiler_sha256` and a `git_state_sha256` of **the tree performing the
admission**. There is no field for the tree, commit, or run that BUILT the
parent. A parent imported from another worktree at an older commit produces a
receipt that silently associates it with the current git state — the receipt
reads as if the parent came from this source. A provenance gate that cannot
express "imported parent" is itself the finding.

Workaround used on 2026-08-18: extra free-text lines were added to the
hand-written `stage2-provenance.receipt` (the gate only `grep -Fq`s for the
`stage2-provenance: pure-simple` marker, so additional lines survive). Those
lines are NOT carried into the v2 receipt — only the file's sha256 is.

## 4. Naming trap worth recording

`stage2-runtime-authority` under `build/bootstrap/stage3/<triple>/` is the
frozen **Rust** authority (`bootstrap-from-scratch.sh:1766`,
`bootstrap_stage3_copy_authority` from the Rust runtime authority), i.e. every
stage2 compiler is seed-BUILT. The gate's `pure-simple` axis is about the
artifact (a compiler compiled from Simple source) versus the seed binary
itself (`grep -Fq 'rust-seed'` -> `parent-compiler-is-rust-seed`), not about
what compiled it. Reading `pure-simple` as "built by a Simple compiler" makes
the gate look unsatisfiable when it is not.

## Fix directions

- Have `bootstrap-from-scratch.sh` emit `stage2-sanity.receipt` /
  `stage2-provenance.receipt` next to the stage2 it produces, so the receipts
  have a real producer.
- Add an explicit bootstrap-genesis mode (or a `--no-parent` admission path)
  for a tree with no stage2, so the cycle has a defined entry point.
- Extend the v2 receipt schema with `parent_origin_root`,
  `parent_origin_git_head`, and `parent_is_imported`, and have consumers treat
  an imported parent as a weaker authority rather than an indistinguishable one.

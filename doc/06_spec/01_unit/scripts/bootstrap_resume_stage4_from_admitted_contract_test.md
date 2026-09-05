# Admitted Stage 4 resume contract

The canonical bootstrap wrapper accepts `--resume-stage4-from-admitted=OUTPUT`
only with a planner-authored `//bootstrap:stage4` receipt, `--deploy`, and one
worker. The continuation verifies the canonical Stage 3 provenance and exact
candidate before any Stage 4 process, owns both bootstrap locks, rejects
symlinks and pre-existing Stage 4 outputs, and binds a continuation receipt.

Stage 2 and Stage 3 trees are snapshotted before continuation, compared before
deployment, and compared again after deployment. Only then is the atomic
continuation receipt changed from `prepared` to `pass` with Stage 4,
provenance, deployment, and immutable-snapshot hashes. The path neither stages
nor probes a Rust seed and cannot select a fallback compiler.

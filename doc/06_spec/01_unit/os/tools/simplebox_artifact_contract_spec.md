# Filesystem-Launched Simplebox Artifact Contract

Source: `test/01_unit/os/tools/simplebox_artifact_contract_spec.spl`

Evidence class: `image-admission`. This validates image and loader routing, not
a live guest invocation.

## Scenarios

- Bind the canonical simplebox artifact to implemented applets and bounded file
  I/O owners.
- Require loader authority for `/SYS/BIN/SIMPLEBOX.SMF` and its canonical
  applet paths.
- Reject relative, unrelated, or prefix-confusable executable paths.


# Bootstrap ad-hoc quick check design

Inputs are a verified compiler path, repeatable changed compiler paths,
positive and negative executable fixtures, expected negative diagnostic,
backend, worker count, and local output root.

The classifier chooses the widest required phase. The runner hashes all
authority inputs into `<output>/<lane>-<digest>/`, compiles/runs the positive
fixture, compiles the negative fixture, then writes `receipt.env`. Any timeout,
memory cap, missing artifact, incorrect marker, unexpected negative success,
or diagnostic mismatch fails the check.

The output intentionally cannot be deployed. Exact Stage4 and essential-tools
smoke remain the completion boundary.

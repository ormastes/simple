# Bootstrap ad-hoc quick check architecture

`app.bootstrap_adhoc.policy` is the pure admission owner. It has no filesystem
or process access. `app.bootstrap_adhoc.args` owns deterministic CLI decoding.
`app.bootstrap_adhoc.main` is the application shell: it validates producer
identity, hashes authority inputs, runs bounded positive/negative builds, and
writes a local receipt.

The lane is not a third bootstrap build mode. It invokes the existing
`one-binary` native-build surface for a small feature fixture. Global compiler
owners fail closed to the canonical full Stage4 pipeline.

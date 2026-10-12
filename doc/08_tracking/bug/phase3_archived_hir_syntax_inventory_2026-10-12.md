# Archived HIR bootstrap syntax inventory

A finite bootstrap-support diagnostic parsed 51 changed Simple files from
immutable Git objects at `464eed97a6fa587637efbc702633c7ffd63f2677`, compared
with `9af03a7d3291c8a9044f884b2ecf5bccfb60683a`. It used the actual parser source,
canonical nightly-2026-09-15 toolchain and the seed's 64 MiB worker-stack policy.
The terminal result was 47 parses successful and four parse errors; peak RSS
was 18,132 KiB and process-group quiescence was recorded.

Three source repairs preserve behavior:

- `driver_hir_archive_weave_boundary_v1.spl:65`: `use.boundary_key = key`
  enters import-statement dispatch. Rename only the local variable to
  `accepted_use`; retain the public `owner.use` field and identical encoding,
  publication, keys and pin contents.
- `hir_mono_archive_consumer_v1.spl:237`: a multiline `if` puts its `else` on
  the preceding expression's line. Give the `else` its own branch line, keeping
  the same loader and error value.
- Fixture `hir_collection_archive/support.spl:86`: `loop.body = ...` enters
  loop-statement dispatch. Rename only the local function record to
  `loop_function`, preserving symbols, spans, loop body and observation values.

The fourth error is a Rust-parser support limitation on the runtime fixture
payload `hir_archive_weave_boundary/provider.spl:4`. Its `@layer_field(w)`
annotation is consumed by the actual Simple frontend's layer-field registry;
Rust `Field` has no corresponding annotation carrier and its struct parser
expects an attributed method here. Preserve the annotation, field default37
and actual mapping tests. Removing them would erase intended coverage. This
diagnostic does not establish that the Simple frontend rejects the payload.

The immutable 51-file source manifest, exact spans, tool hashes and receipts
are in `C:/dev/simple-phase3-runner-mir-evidence/context-comparison-parser/`.
Earlier private harness failures from CRLF path arguments and the default
Windows stack are preserved separately; they are not source parse verdicts.
This inventory is syntax support only. Compiler admission, native fixture
execution, Hello World and full runner/MCP/LSP qualification remain pending.

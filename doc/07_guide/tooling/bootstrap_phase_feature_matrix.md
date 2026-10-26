# Phase 1 and Phase 2 major-feature matrix

`scripts/check/check-bootstrap-phase-feature-matrix.py` is the fixed Phase 1/2
controller for compiler, interpreter, and major tool behavior. It does not
build, discover, publish, or promote an artifact. Run it only after the phase
owner supplies a newly admitted generation and all declared executable hashes.

The controller never invokes `simple`, an MCP server, or another product tool
through `PATH`. Every supported row names an artifact whose path is absolute,
whose bytes match SHA-256 before and after launch, and whose generation,
provenance, and admission envelope match the phase compiler. Script wrappers,
symlinks, stale Phase 1 tools, and cross-generation Phase 2 companions fail
before process creation even if an equivalent ambient tool would pass.

Phase 1 and Phase 2 receipts always set `release_evidence=false`. A Rust seed or
an intermediate pure-Simple receiver can establish phase-scoped diagnostics;
neither is Stage 4 or release evidence.

## Required rows

Each suite family has an interpreter and native row:

| Family | Required behavior |
|---|---|
| `compiler` | Focused compiler/bootstrap semantics |
| `language_runtime` | Representative syntax, values, collections, errors, functions, generics, concurrency, IO, and runtime behavior |
| `simple_mcp` | MCP unit/integration behavior |
| `simple_lsp_mcp` | LSP MCP unit/integration behavior |
| `t32_mcp` | TRACE32 MCP schema, dispatch, guard, and lifecycle behavior |
| `spipe_sspec` | SPipe runner, SSpec assertions, docgen, and zero-stub behavior |
| `caret` | LLM Caret room, routing, profile, receipt, and messaging behavior |
| `slang` | Slang model loading, packing, server, and local-model behavior supported by the phase |
| `simd_db_web` | SIMD scalar parity plus representative database and HTTP/web behavior |
| `devhub` | DevHub dispatch, provider adapters, and offline contracts |

Ten additional rows actually launch admitted binaries or retain provider
availability evidence: `simple_mcp_protocol`,
`simple_lsp_mcp_protocol`, `t32_mcp_protocol`, `spipe_plugin_launch`,
`caret_protocol`, `slang_binary_launch`, `devhub_launch`, `devhub_github`,
`devhub_jira`, and `devhub_confluence`. MCP rows perform initialize and
tools/list exchanges and require a declared tool inventory; optional tool calls
must be read-only. The installed SPipe plugin row launches its admitted runtime
with a separately hash-bound plugin entry and checks meaningful guide output.
DevHub provider rows use read-only resource lookups. Missing provider credentials
or resource selectors are BLOCKED; malformed responses and dispatch failures are
FAIL.
Only the controller-owned GitHub, Jira, and Confluence rows may classify an
anchored 401/403, explicit unauthenticated status, missing provider CLI, or
specific DNS/network failure as BLOCKED. Manifest-provided words such as
`login`, `token`, or `error` cannot downgrade a nonzero implementation or
dispatch failure. A negative exit or exit status 128 and above is always a
FAIL, even when output before the crash contained an exact unauthorized status.

Missing rows are failures. A phase may declare a row `unsupported` or `blocked`
only with `reason`, `owner`, `reviewer`, and `prerequisite`. Such a row does not launch and
cannot count as PASS. Its receipt still binds the phase compiler identity and
contains an exact `resume_argv` for a fresh evidence directory.

## Manifest and admission binding

The manifest schema is `BootstrapPhaseFeatureManifestV1` and accepts only phase
1 or 2. It contains:

- `phase` and a nonempty immutable `generation` identity;
- `bootstrap_jobs.selected` and `bootstrap_jobs.detected_cpu_count`;
- a sorted, unique, nonempty `capability_set` bound into admissions and receipts;
- for Phase 1, the exact `current_authority` binding for
  `src/compiler_rust/target/bootstrap.current.env`;
- for Phase 1, the exact `handoff` binding supplied by the producing bootstrap
  continuation;
- `compiler` and optional named `artifacts`;
- exactly one declaration for every required row.

Every compiler or artifact binding contains `path`, `sha256`, `generation`,
`provenance: {path, sha256}`, and `admission: {path, sha256}`. Its admission
envelope uses `BootstrapPhaseFeatureAdmissionV1` with the same phase,
generation, absolute artifact path, artifact SHA-256, producing compiler
SHA-256, provenance SHA-256, capability-set SHA-256, and `status: ADMITTED`. This envelope records an
already-admitted artifact; it does not replace bootstrap provenance or sanity
admission.

The Phase 1 compiler is the exception to the generic JSON envelope: both its
provenance and admission bindings must name the exact immutable handoff with
schema `simple-bootstrap-phase1-current-handoff-v1` and status
`current-committed`. The handoff must reproduce the compiler path/hash, current
marker path/hash, generation, seed-stamp path/hash, selected jobs, and detected
CPU count. The controller validates the handoff and current marker before and
after every launch.

For Phase 1, the controller also revalidates the current-authority marker and
its transaction absence before and after every launched row. The marker's
generation and input fingerprint must select exactly one immutable generation
stamp, and that stamp and seed must hash to the matrix compiler. Supplying a
fully self-consistent older Phase 1 manifest therefore still fails once the
repository current pointer advances.

A supported row repeats `artifact_sha256`, `generation`,
`provenance_sha256`, and `admission_sha256`. This redundant row pin is the stale
tool gate: changing an artifact map entry cannot silently retarget old row
configuration. Suite rows also carry a sorted list of exact test `{path,
sha256}` bindings. The controller constructs the full test command itself and
adds `--mode=interpreter` or `--mode=native`, `--assert-ran`, no cache/daemon,
sequential execution, and fail-fast. PASS requires a nonzero `Results:` total,
all tests passed, zero failed, and no stub/source/PATH fallback marker.

Command rows contain an admitted executable artifact, literal `args`, nonempty
`expected_stdout`, and any additional hash-bound `inputs`. Protocol rows contain
`expected_tools` and may contain a read-only `call` object. `argv[0]` is always
the validated absolute artifact path.

## Preparation and execution

Validate a frozen manifest without launching rows:

```sh
python scripts/check/check-bootstrap-phase-feature-matrix.py \
  --manifest /absolute/phase-feature.json \
  --output /absolute/evidence/not-used \
  --validate-only
```

After the phase owner admits the artifact and authorizes row execution, use a
fresh output directory:

```sh
python scripts/check/check-bootstrap-phase-feature-matrix.py \
  --manifest /absolute/phase-feature.json \
  --output /absolute/evidence/phase-2-major-features \
  --timeout 120
```

Resume only a changed failed, blocked, or unsupported row using its exact
`resume_argv`. Never reuse a receipt directory. A changed manifest, executable,
test inventory, admission, provenance receipt, phase generation, job count, or
CPU count requires a new matrix run.

Each `BootstrapPhaseFeatureRowV1` receipt records compiler and launched
executable paths/hashes, admission and provenance paths/hashes, generation,
full argv and its hash, inventory and its hash, selected job count, detected CPU
count, capability-set hash, owner, reviewer, PID, duration, exit status, output
hashes, result, reason, and resume
argv. `summary.json` uses `BootstrapPhaseFeatureMatrixV1` and counts PASS, FAIL,
BLOCKED, and UNSUPPORTED without converting unavailable rows to green.

Controller fixtures are in
`test/01_unit/scripts/bootstrap_phase_feature_matrix_test.py`. They exercise
stale generation/hash rejection, absolute native executable enforcement,
required row coverage, job evidence, unavailable receipts, and one synthetic
exact-executable launch. They never qualify a bootstrap artifact.

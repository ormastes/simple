# Bootstrap phase live service checks

`scripts/check/check-bootstrap-phase-live.py` is host verification orchestration,
not a product runtime or a replacement for SPipe suites. It launches explicitly
admitted artifacts without building, publishing, choosing a seed, or using a
raw Simple source entrypoint. Python 3.9+ is required on the verification host.

Run once for each admitted phase, using a new evidence directory:

```sh
python scripts/check/check-bootstrap-phase-live.py --manifest /absolute/phase-live.json --output /absolute/evidence/phase-4
```

The manifest schema is `BootstrapPhaseLiveManifestV1`. Fields:

| Field | Meaning |
|---|---|
| `phase` | Integer 1 through 5; no evidence carries across phases |
| `compiler` | Exact phase driver `{path, sha256}`; Stage 4 uses the candidate full CLI |
| `artifacts` | Optional entries `mcp`, `lsp_mcp`, `spipe_plugin`, `caret`, `devhub` |
| `spipe_plugin_entry` | Pinned plugin CLI script `{path, sha256}` |
| `github_cli` | Reference GitHub CLI `{path, sha256}` for authenticated identity comparison |
| `resources` | `jira` issue key, `confluence` page ID, `github` owner/repository |
| `resources.*_principal` | Expected Jira/Confluence account ID or GitHub login, respectively |
| `resources.confluence_identity_url` | HTTPS current-user endpoint ending `/rest/api/user/current` |

Each artifact entry includes `{path, sha256, admission: {path, sha256}}`.
The phase owner supplies an admission JSON document with schema
`BootstrapPhaseArtifactAdmissionV1`, exact `phase`, `status: ADMITTED`,
`artifact_sha256`, `compiler_sha256`, and `evidence: {path, sha256}` referring
to the authoritative build/admission evidence. This binding envelope does not
replace the bootstrap provenance verifier; create it only after that verifier
admits the product. The live checker cannot itself prove compiler provenance.
All paths are absolute. Credentials stay in the operator's normal credential
home or environment; never put tokens or credential commands in the manifest.

`mcp` and `lsp_mcp` are native stdio servers. `caret` is the compiled messaging
MCP worker; its read-only probe is `chat_who`. `devhub` is the native standalone
DevHub artifact. `spipe_plugin` binds the host plugin runtime executable and
launches the pinned entry with `self-review-guide`. This verifies plugin launch;
the named SPipe suite and docgen gates still verify application behavior.

The controller performs ordered MCP initialize, initialized notification, and
tools/list exchanges, then calls Simple search or Caret profile inspection.
DevHub must advertise its actual provider commands. Jira and Confluence must
return the expected authenticated principal and read the configured resource.
GitHub uses the bound reference `gh api user` for identity and the actual
DevHub `github repo view` command for the resource read. DevHub's current
`github` handler does not implement `api user`; this check does not claim it
does. No messages, issues, pages, or repositories are created or changed.

Each row produces `BootstrapPhaseLiveReceiptV1` JSON: phase, manifest/artifact
digests, launched flag, PID, actual argument vector, response digests, duration,
status/reason, and an exact `resume_argv` targeting a fresh directory. Response
bodies and credentials are not retained. Missing artifacts are `UNSUPPORTED`;
missing resources/identity setup, unavailable authentication, and timeouts are
`BLOCKED`. Error JSON, mismatched identities/resources, crashes, and digest
drift fail. Exit 0 requires every requested row to pass, 1 denotes failure,
and 2 denotes unavailable rows. Unavailable rows remain release blockers.

Provider output is classified as unavailable only for the fixed GitHub, Jira,
and Confluence rows and only for anchored 401/403, explicit unauthenticated,
missing provider CLI, or typed DNS/network/connectivity failures. Help text or
incidental words such as `login`, `token`, `authentication`, and `request
failed: http parser` do not mask implementation failures. Negative exits and
statuses 128 or above are crashes and always FAIL, including when earlier
output contained a valid unauthorized line.

Run the standalone controller against admitted Stage 4 artifacts after the
named suites and protocol gates. Automatic integration into the Stage 4 tooling
matrix is separate work; this controller does not add a matrix admission row.
Compiler/interpreter tests, Caret/DevHub/SPipe full suites, startup/RSS NFRs,
deployment verification, and cross-host acceptance remain separate gates.

Controller verification:

```sh
python test/01_unit/scripts/bootstrap_phase_live_test.py
```

Its eleven tests use synthetic child fixtures exclusively to test the checker;
they are never live service or bootstrap admission evidence.

Phase 1 matrix tools require the current committed Rust seed generation from
`src/compiler_rust/target/bootstrap.current.env`. Before snapshotting, the
runner verifies the generation directory and its seed stamp. Each actual tool
launch then rechecks the current commit record, stamp, producer bytes, and
the registered executable SHA-256. Only the compiler snapshot and artifacts
produced by that same matrix may execute. Bare PATH names, older compiler
bytes, replaced tools, and a changed or pending authority publication fail
before execution; successful tools are checked again after execution.

Every launch writes `.phase1-before.env` and, on success, `.phase1-after.env`
beside its task log, recording executable path/hash, producer path/hash,
generation, and admission receipt path/hash. The phase summary records the
same admitted generation. `--hash-policy=temporary` cannot weaken this Phase 1
gate. The focused checks are
`test/01_unit/scripts/bootstrap_phase1_current_authority_test.shs` and
`test/01_unit/scripts/bootstrap_phase_stage1_native_build_authority_test.shs`.

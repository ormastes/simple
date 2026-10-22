# Coverage-aware retained parser ownership test plan

Run [the executable spec](../../../test/03_system/compiler/coverage_retained_parse_owner_spec.spl)
through the existing native AOT test runner with artifacts retained. Set `SIMPLE_NO_STUB_FALLBACK=1` and
`SIMPLE_QUALIFIED_RUNTIME` to a canonical source-matched pure-Simple CLI with
its genuine `.provenance.env`. The existing Stage4 provenance verifier owns
admission; a Rust seed, missing receipt or arbitrary supplied hash cannot pass.

The spec compiles the actual native fixture once into a private
`build/test-artifacts/coverage-retained-parse-owner-<pid>-<time>/` directory and
runs `--coverage`, `--mcdc`, and `--full-inventory` in separate processes.
Compiler and fixture stdout/stderr, binary/source hashes and exit statuses are
retained. Native fixture bytes are hashed before and after each execution.

| Requirement | Coverage scenario | MC/DC scenario | Full-inventory scenario |
|---|---|---|---|
| REQ-PARSE-OWNER-001 | Four source scopes and retained body | Same under MC/DC | Same with target selection |
| REQ-PARSE-OWNER-002 | Original rows and desugared functions | Exact condition/context replay | Original rows and four valid receipts |
| REQ-PARSE-OWNER-003 | Malformed diagnostic then recovery | Malformed diagnostic then recovery | Missing authority plus malformed recovery |

Each mode checks actual AST counters after teardown and reads the first
retained body after later allocations. The fixture uses an x86_64 Linux
frontend target for receipt validation; this is not cross-target codegen proof.

Current status: **UNRUN**. The stronger SSpec admission is blocked until its
canonical full CLI provenance is available. The unchanged direct fixture may
first run as a Stage2 bootstrap diagnostic when the campaign owner verifies
its real source/runtime admission receipt. Such a result must be reported
separately; it does not satisfy this SSpec wrapper's Stage4 admission.

After a qualified host is available, run the spec once, then run
`simple spipe-docgen test/03_system/compiler/coverage_retained_parse_owner_spec.spl --output doc/06_spec --no-index`.
Require completion with zero stubs. The authored manual currently records
the intended scenarios and makes no generated-docgen or execution PASS claim.

The whole-object build, tree RSS cap, exact link membership and executable
Hello World remain separate acceptance gates. No fixture result substitutes
for those gates.

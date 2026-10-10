# Spec facade owner regression setup

REQ-SSPEC-FACADE-001: file and package entrypoints bind one stateful spec owner. Enumeration suppresses callbacks; native run records deliberate failures. The native fixture initializes its own runtime mode and does not mutate its parent's environment. Each scenario owns its evidence filenames; the run scenario creates its own enumeration baseline and can be selected independently.

Build the real fixture with the compiler under test, using its admitted native backend/runtime:

```
<compiler> native-build --backend=<supported-backend> --source src --source test/fixtures/lib --entry-closure --entry test/fixtures/lib/spec_facade_control.spl --output <owned-output>/spec-facade-control
```

Set `SIMPLE_SPEC_FACADE_NATIVE_BINARY` to that built executable and `SIMPLE_SPEC_FACADE_EVIDENCE_DIR` to a new, empty directory owned by this run. Then execute:

```
<test-runtime> test test/02_integration/lib/spec_facade_owner_spec.spl
```

The test explicitly fails for missing configuration, failed child execution, stale evidence files, incorrect registry identities/counts, body output during enumeration, parent-mode changes, or lost intentional failures. It never substitutes a mock executable or silently skips an unavailable compiler. A missing native build is a blocked prerequisite, not test success. For a failed-only selection of the second example, use a fresh evidence directory; no first-example output is needed.

The child run intentionally returns 1 and produces one passing and two failing registry rows. Both SSpec examples must pass by checking that contract. Source-interpreting the fixture is not equivalent: the seed intercepts internal fail_assertion into separate BDD state. Keep that known diagnostic failure separate from actual native behavior. Seed-built native evidence does not qualify a pure-Simple successor or all six subsystem products.

## Reproducible Windows setup

Supply an already verified compiler in `SIMPLE_SPEC_COMPILER` and a source-capable test runtime in `SIMPLE_SPEC_TEST_RUNTIME`. Phase 1 diagnostic use must name its immutable seed explicitly; no seed fallback is performed. Choose a supported backend in `SIMPLE_SPEC_BACKEND` (`llvm` for the qualified pure Windows producer, or `cranelift` for the diagnostic seed used in the evidence).

```powershell
if (-not $env:SIMPLE_SPEC_COMPILER -or -not $env:SIMPLE_SPEC_TEST_RUNTIME -or -not $env:SIMPLE_SPEC_BACKEND) { throw 'Set the verified compiler, test runtime and supported backend' }
if ($env:SIMPLE_SAFETY_PROFILE -eq 'critical') { throw 'Use the default non-critical profile for callback-execution acceptance; critical skip rejection has separate specs' }
$facadeRun = Join-Path (Get-Location) ('build/spec-facade-' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $facadeRun | Out-Null
$facadeBinary = Join-Path $facadeRun 'spec-facade-control.exe'
& $env:SIMPLE_SPEC_COMPILER native-build --backend $env:SIMPLE_SPEC_BACKEND --source src --source test/fixtures/lib --entry-closure --entry test/fixtures/lib/spec_facade_control.spl --output $facadeBinary
if ($LASTEXITCODE -ne 0) { throw 'Native fixture build failed; do not run the spec' }
$facadeEvidence = Join-Path $facadeRun 'evidence'
New-Item -ItemType Directory -Path $facadeEvidence | Out-Null
$env:SIMPLE_SPEC_FACADE_NATIVE_BINARY = $facadeBinary
$env:SIMPLE_SPEC_FACADE_EVIDENCE_DIR = $facadeEvidence
& $env:SIMPLE_SPEC_TEST_RUNTIME test test/02_integration/lib/spec_facade_owner_spec.spl
if ($LASTEXITCODE -ne 0) { throw 'Facade ownership regression failed' }
```

Retain the run directory for failure analysis. A subsequent full or failed-only run must create a new evidence directory; do not delete or overwrite a previous run's ledgers. The fixture sets only its child-local runtime mode to native. The parent mode and assurance profile remain unchanged; assurance-profile policy continues to govern skip behavior.

This callback-execution acceptance uses the default/non-critical `SIMPLE_SAFETY_PROFILE`. The critical profile deliberately rejects metadata-free skip_it before its callback; that separate policy is not qualified by these two examples.

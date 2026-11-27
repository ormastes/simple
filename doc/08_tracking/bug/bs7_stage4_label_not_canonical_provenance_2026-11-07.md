# BS7 canonical Stage4 authority

BS7 previously required `stage=4` and rejected `seed`/`rust` substrings in a
supplied `compiler_kind`. Actual bootstrap provenance does not emit this
two-field format; the unit fixture invented it. Hashing a label did not validate
the compiler, source or parent authority, and actual canonical provenance could
not be supplied directly.

Both BS7 entrypoints now require `--stage4-compiler` and
`--stage4-source-root` alongside `--stage4-receipt`. The receipt must be the
actual adjacent `simple-bootstrap-stage4-provenance-v1` sidecar for a
`pure-simple-full-cli` candidate. The unmodified existing
`stage4_verify_candidate_provenance` validates it, including deep Stage3 checks.
The producer forwards these arguments to its final checker. No Phase2 Hello or
retained-manual/self receipt is converted into canonical Stage4 admission.
The measured NoGC Hello and interpreter remain separate from the compiler.
The cohort v1 schema and size/link/stdout/sample/percentile/RSS checks remain.

## Contract tests, not native qualification

The existing unit fixture copies production BS7 scripts and the **unmodified**
canonical Stage4 verifier into a private protocol tree. Its private copied
Stage3 facade stubs only the deep Stage3 dependency, checks arguments, records
calls and can refuse verification. Synthetic compiler/source/parent/provenance
bytes are never executed or published as bootstrap authority. Production has
no test flag, substitute verifier or admission bypass.

The final bounded run accepted the contract cohort, rejected old two-field
labels at both entrypoints, propagated deep-verifier refusal, and rejected
compiler/parent/Stage3/source/helper/build/smoke mutations. Existing matched
link/stdout/sample guards passed. This does not qualify any Simple executable.

Three verification cycles were used, with original failures retained. First,
the old synthetic runtime's libc imports exceeded the unchanged 1.05x fixture
limit with Clang 23. The fixture shim now uses `puts` for its one known
NUL-terminated literal; production runtime semantics are untouched. The second
run reported an accepted mutation without identifying its location. Inspection
found the existing archive mutation changed only its first digest nibble and
could be a no-op; it now writes a guaranteed-invalid all-zero digest. The third
run passed. No further green reruns were performed.

## OPEN: measurement and no-demand acquisition

BS7 still consumes supplied raw samples, NoGC inventory and provider-effect
trace. It does not collect startup/RSS, prove the workload was built by this
compiler, or establish zero mappings/initialization/archive reads from an empty
trace. Real finite acquisition, exact compiler/runtime/build bindings, and
owner-backed no-demand observations remain required for I5-01/08/11/12.
Existing vector events cover their vector subset only. No native cohort,
application performance or complete minimum-image qualification is claimed.

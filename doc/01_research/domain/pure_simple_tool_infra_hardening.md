<!-- codex-research -->
# Pure-Simple tool and infrastructure hardening: domain research

Date: 2026-07-16

## Relevant established practices

### Exit codes are part of the test-runner contract

Pytest documents distinct exit codes for passing tests, test failures,
interruptions, internal errors, usage errors, and empty collection. Simple does
not need identical numbers, but it needs the same unambiguous separation so an
empty or internally broken run cannot look green.

Source: https://docs.pytest.org/en/stable/reference/exit-codes.html

### Format checking must be a non-mutating gate

Clang-format exposes dry-run/error behavior separately from in-place edits and
can fail incomplete formatting. Simple's `fmt --check` should likewise be
deterministic, non-mutating, and return nonzero on drift or formatter failure.

Source: https://clang.llvm.org/docs/ClangFormat.html

### Caches are accelerators, never correctness authorities

GitHub's official cache guidance distinguishes reusable caches from retained
artifacts, requires cache misses to remain recoverable, and warns that restored
cache content is untrusted. Simple test/compile caches therefore need content- or
dependency-keyed invalidation, regeneration on miss, and no secrets/executable
trust without validation.

Source: https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching

### Do not pass CLI paths through a shell

OWASP identifies command injection as the result of passing unsafe user input to
a system shell and recommends using the language's existing APIs instead. This
directly applies to duplicate-check: directory walking and file reading already
exist as Simple APIs, so escaping a constructed `find`/`cat` command would be a
weaker and more complex fix than deleting the shell boundary.

Source: https://owasp.org/www-community/attacks/Command_Injection

### Qualification tests should be hermetic

Bazel's test execution specification explains that undeclared environmental
dependencies reduce reproducibility, auditability, and resource isolation.
Simple's production qualification fixtures should therefore declare their
inputs, use isolated output roots, and never depend on ambient seed/debug paths.

Source: https://docs.bazel.build/versions/3.5.0/test-encyclopedia.html

### Deployed artifacts need independently verifiable provenance

The Reproducible Builds project defines reproducibility as an independently
verifiable path from source to binary and calls for deterministic outputs plus a
recorded or predefined build environment. A production-looking release path is
not provenance; the deployed Simple binary needs recorded stage/tool hashes and
a runtime identity probe.

Source: https://reproducible-builds.org/docs/

### Tool hardening implication for Simple

The production matrix should assert provenance, exit class, output schema, and
mutation behavior. It should execute cached artifacts only after validating
their provenance. Test and duplicate caches may improve latency but must not turn
missing discovery, parser failure, or stale dependency state into success.

## Applied conclusions

1. Define explicit exit classes for pass, assertion failure, empty discovery,
   usage error, internal error, and timeout/resource termination.
2. Make `fmt --check`, lint, check, and duplication gates non-mutating by
   default; mutation requires an explicit flag.
3. Hash tool version/config/input closure into caches and validate restored
   executable artifacts before use.
4. Treat provenance and hollow-green checks as release blockers, not warnings.

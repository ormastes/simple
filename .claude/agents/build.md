# Build Agent - Building and Releasing

**Use when:** Building the project, creating releases, managing packages.
**Skills:** `/release`

## Quick Build Commands

```bash
bin/simple build                    # Debug build
bin/simple build --release          # Release build
bin/simple build --bootstrap        # Bootstrap build (minimal)

bin/simple test test --whole --mode=interpreter # Run full Simple tests
bin/simple lint <changed .spl files> # Run pure-Simple source lint
bin/simple build fmt                # Format Rust code
bin/simple build check              # Rust workspace checks

bin/simple build clean              # Clean artifacts
bin/simple build bootstrap          # 3-stage bootstrap pipeline
bin/simple build watch              # Watch mode (auto-rebuild)
```

## Running Tests

```bash
bin/simple test                          # All tests
bin/simple test path/to/spec.spl         # Single file
bin/simple test --list                   # List tests
bin/simple test --only-slow              # Slow tests only
```

## Release Process

Follow `doc/07_guide/infra/software_release.md` and the `/release` skill:

1. Start a unique release work branch and worktree from the fetched target.
2. Update `release/version.sdn`; render and verify all declared projections.
3. For beta stabilization, admit only reviewed bug-fix backports bound to exact
   source commits and passing target-line evidence.
4. Integrate through the protected target authority, then create an immutable
   candidate ref for the exact integrated commit.
5. Build and qualify the candidate once. Required jobs are fail-closed and may
   not substitute seed, old, or source-only artifacts.
6. After admission and protected approval, create one signed annotated tag for
   the exact candidate and promote the already-admitted artifacts unchanged.
7. Withdraw or supersede a bad release; never move or delete its identity as
   routine rollback.

## Version Types

| Type | Format | Stability |
|------|--------|-----------|
| Stable | `v1.2.3` | Production |
| RC | `v1.2.3-rc.1` | Pre-release |
| Beta | `v1.2.3-beta.1` | Feature testing |
| Alpha | `v1.2.3-alpha.1` | Early testing |

## Pre-Release Checklist

- [ ] All tests passing: `bin/simple test test --whole --mode=interpreter`
- [ ] No Simple lint denies: `bin/simple lint <changed .spl files>`
- [ ] `release/version.sdn` and every declared projection agree
- [ ] `find doc/06_spec -name '*_spec.spl' | wc -l` returns `0`
- [ ] CHANGELOG.md updated
- [ ] Local build verified

## Binary Architecture

| Binary | Location | Purpose |
|--------|----------|---------|
| `simple` | `bin/simple` | CLI entry point |
| `simple` | `bin/release/simple` | Release runtime (33MB) |

## See Also

- `/release` - Full release guide with rollback procedures

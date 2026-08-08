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

1. Update version in `VERSION`, `src/app/cli/main_part1.spl`, and `src/app/cli/bootstrap_main.spl`
2. Update `CHANGELOG.md`
3. Commit: `jj commit -m "chore: Release vX.Y.Z"`
4. Tag: `git tag -a vX.Y.Z -m "Release vX.Y.Z"` (use git for tags)
5. Push: `jj bookmark set main -r @- && jj git push --bookmark main && git push origin vX.Y.Z`
6. Monitor GitHub Actions
7. Verify: `gh release view vX.Y.Z`

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
- [ ] Version updated in all 3 version sources
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

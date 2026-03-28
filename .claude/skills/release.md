# Release Skill

## Release Types

| Type | Format | Stability |
|------|--------|-----------|
| Stable | `v1.2.3` | High |
| RC | `v1.2.3-rc.1` | Medium-High |
| Beta | `v1.2.3-beta.1` | Medium |
| Alpha | `v1.2.3-alpha.1` | Low |

## Pre-Release Checklist

- [ ] `bin/simple test` passing
- [ ] `bin/simple build lint` clean
- [ ] `bin/simple todo-scan` -- no critical TODOs
- [ ] `CHANGELOG.md` updated
- [ ] Version in `simple.sdn` updated
- [ ] Local bootstrap build works

## Release Process

```bash
# 1. Update version in simple.sdn
# 2. Update CHANGELOG.md
# 3. Commit
jj commit -m "chore: Release vX.Y.Z-rc.N"
# 4. Tag (git for tags)
git tag -a vX.Y.Z-rc.N -m "Release vX.Y.Z-rc.N"
# 5. Push
jj bookmark set main -r @- && jj git push --bookmark main
git push origin vX.Y.Z-rc.N
# 6. Monitor GitHub Actions
# 7. Verify
gh release view vX.Y.Z-rc.N
gh release download vX.Y.Z-rc.N --pattern "*-linux-x86_64.spk"
```

## Post-Release

- Verify packages download + install on clean system
- Check GHCR packages published
- Announce in project channels
- Mark as pre-release for RC/beta/alpha

## Rollback

```bash
gh release delete vX.Y.Z-rc.N --yes
git tag -d vX.Y.Z-rc.N
git push origin :refs/tags/vX.Y.Z-rc.N
```

## Version Progression

```
alpha.1 -> alpha.2 -> beta.1 -> beta.2 -> rc.1 -> rc.2 -> stable
```

RC = "Ready for release unless critical issues found." No new features, API locked.

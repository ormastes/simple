# Release Skill

**Purpose**: Guide through creating Simple language releases (stable, RC, beta, alpha)

---

## Release Types

| Type | Version Format | Use Case | Stability |
|------|---------------|----------|-----------|
| **Stable** | `v1.2.3` | Production use | High |
| **RC** | `v1.2.3-rc.1` | Pre-release testing | Medium-High |
| **Beta** | `v1.2.3-beta.4` | Feature testing | Medium |
| **Alpha** | `v1.2.3-alpha.2` | Early testing | Low |

---

## Pre-Release Checklist

### Code Quality
- [ ] All tests passing: `simple test`
- [ ] No lint warnings: `simple build rust lint`
- [ ] Code formatted: `simple build rust fmt --check`
- [ ] No critical TODOs: `simple todo-scan`

### Documentation
- [ ] `CHANGELOG.md` updated with changes
- [ ] Version number updated in `simple.sdn`
- [ ] README accurate for this version
- [ ] Breaking changes documented

### Build Verification
- [ ] Local bootstrap build works: `./script/build-bootstrap.sh`
- [ ] Package structure correct (symlink present)
- [ ] Binary sizes reasonable
- [ ] All platforms tested (if possible)

---

## Release Process

### Step 1: Update Version

**For RC release:**
```bash
# Edit simple.sdn
# Change version: 0.5.0-alpha to 0.5.0-rc.1
```

**Version format:**
- Stable: `0.5.0`
- RC: `0.5.0-rc.1`, `0.5.0-rc.2`, etc.
- Beta: `0.5.0-beta.1`, `0.5.0-beta.2`, etc.
- Alpha: `0.5.0-alpha.1`, `0.5.0-alpha.2`, etc.

### Step 2: Update CHANGELOG.md

```markdown
## [0.5.0-rc.1] - 2026-02-05

### Added
- Feature descriptions

### Changed
- Change descriptions

### Fixed
- Bug fix descriptions
```

### Step 3: Commit Changes

```bash
# Stage changes
jj commit -m "chore: Prepare release v0.5.0-rc.1"
```

### Step 4: Create Tag

```bash
# Create bookmark (jj equivalent of git tag)
jj bookmark set v0.5.0-rc.1 -r @

# Or for git compatibility
jj git push --bookmark main  # Push main first
git tag -a v0.5.0-rc.1 -m "Release v0.5.0-rc.1"
```

### Step 5: Push to GitHub

```bash
# Push changes and tag
jj git push --bookmark main
jj git push --bookmark v0.5.0-rc.1

# Or with git
git push origin main
git push origin v0.5.0-rc.1
```

### Step 6: Monitor GitHub Actions

1. Go to: `https://github.com/OWNER/simple/actions`
2. Watch "Release" workflow
3. Check for:
   - ✅ Build bootstrap (3 platforms)
   - ✅ Build full package
   - ✅ Test installation (2 platforms)
   - ✅ Create release
   - ✅ Publish to GHCR

### Step 7: Verify Release

```bash
# Check release page
gh release view v0.5.0-rc.1

# List assets
gh release view v0.5.0-rc.1 --json assets

# Download and test package
gh release download v0.5.0-rc.1 --pattern "*-linux-x86_64.spk"
tar -tzf simple-bootstrap-*-linux-x86_64.spk | grep "^./bin"
# Should show:
# ./bin/simple
```

### Step 8: Test Installation

```bash
# Extract package
mkdir -p /tmp/test-release
tar -xzf simple-bootstrap-*-linux-x86_64.spk -C /tmp/test-release

# Test binaries
/tmp/test-release/bin/simple --version
```

---

## Post-Release Tasks

### Immediate
- [ ] Verify all packages downloaded successfully
- [ ] Test installation on clean system
- [ ] Check GHCR packages published
- [ ] Update documentation links if needed

### Communication
- [ ] Announce in project channels
- [ ] Update release notes if issues found
- [ ] Mark as pre-release for RC/beta/alpha

### Follow-up
- [ ] Monitor for issues
- [ ] Track feedback
- [ ] Plan next release (stable/RC)

---

## Rollback Procedure

If release has critical issues:

```bash
# Delete release
gh release delete v0.5.0-rc.1 --yes

# Delete tag locally and remotely
jj bookmark delete v0.5.0-rc.1
jj git push --bookmark v0.5.0-rc.1 --delete

# Or with git
git tag -d v0.5.0-rc.1
git push origin :refs/tags/v0.5.0-rc.1
```

---

## Common Issues

### Issue: GitHub Actions Fails

**Check**: Workflow logs at `https://github.com/OWNER/simple/actions`

**Common causes**:
- Previous release download failed (first-time bootstrap)
- Cargo build error (dependency issues)
- Permission issues (GITHUB_TOKEN)

**Solution**:
```bash
# Re-run failed jobs in GitHub Actions UI
# Or delete tag and try again
```

### Issue: Package Missing Files

**Check**: Download and inspect package

```bash
tar -tzf simple-bootstrap-*.spk | less
```

**Solution**: Verify `script/build-bootstrap.sh` creates symlink

### Issue: Symlink Not Preserved

**Check**: Extract and verify

```bash
tar -xzf simple-bootstrap-*.spk -C /tmp/test
ls -lh /tmp/test/bin/
```

**Solution**: Ensure using `tar -czf` (not `zip` or other format)

---

## Release Checklist Template

Copy this for each release:

```markdown
## Release v0.5.0-rc.1 Checklist

### Pre-Release
- [ ] Tests passing
- [ ] Lint clean
- [ ] Version updated in simple.sdn
- [ ] CHANGELOG.md updated
- [ ] Local build verified

### Release
- [ ] Committed: `jj commit -m "chore: Release v0.5.0-rc.1"`
- [ ] Tagged: `jj bookmark set v0.5.0-rc.1 -r @`
- [ ] Pushed: `jj git push --bookmark v0.5.0-rc.1`
- [ ] GitHub Actions completed
- [ ] Release created on GitHub

### Verification
- [ ] Downloaded packages
- [ ] Verified bin/simple works
- [ ] GHCR packages published

### Post-Release
- [ ] Announced release
- [ ] Updated docs
- [ ] Marked as pre-release (RC)
```

---

## Version Progression

Example progression for v0.5.0:

```
v0.5.0-alpha.1  → First implementation
v0.5.0-alpha.2  → Bug fixes
v0.5.0-beta.1   → Feature complete
v0.5.0-beta.2   → More testing
v0.5.0-rc.1     → Release candidate (this guide)
v0.5.0-rc.2     → Critical fixes only
v0.5.0          → Stable release
```

---

## Commands Reference

```bash
# Check current version
grep "version:" simple.sdn

# Update version (edit file)
# Then commit
jj commit -m "chore: Release vX.Y.Z-rc.N"

# Create tag
jj bookmark set vX.Y.Z-rc.N -r @

# Push
jj git push --bookmark main
jj git push --bookmark vX.Y.Z-rc.N

# Check release status
gh release view vX.Y.Z-rc.N

# Download and test
gh release download vX.Y.Z-rc.N --pattern "*-linux-x86_64.spk"
tar -xzf simple-bootstrap-*.spk -C /tmp/test
/tmp/test/bin/simple --version
```

---

## RC-Specific Notes

### What is RC?

Release Candidate = "Ready for release unless critical issues found"

**Criteria for RC**:
- All planned features implemented
- All tests passing
- No known critical bugs
- Documentation complete
- Ready for production testing

**RC Testing Period**: Usually 1-2 weeks

**RC → Stable**:
- If no critical issues found: Promote to stable
- If critical issues found: Fix and create RC.2

### RC vs Beta

| Aspect | Beta | RC |
|--------|------|-----|
| **Stability** | Medium | High |
| **Feature Changes** | Allowed | No new features |
| **API Changes** | Possible | Locked |
| **Testing Focus** | Features | Stability |
| **Next Step** | More beta or RC | Stable or new RC |

---

## Example: v0.5.0-rc.1 Release

Based on current changes (binary structure, script migration):

```bash
# 1. Update version
# Edit simple.sdn: version: 0.5.0-rc.1

# 2. Update CHANGELOG.md
cat >> CHANGELOG.md <<EOF
## [0.5.0-rc.1] - 2026-02-05

### Added
- Simple scripts (.spl) for build and install

### Changed
- Bootstrap packages now use bin/simple as main binary
- GitHub Actions prefers Simple scripts over bash
- Binary size reduced: 13MB (bootstrap) vs 32MB (regular)

### Fixed
- Install script handles both old and new package formats
- File extension policy clarified (use .spl, not .ssh)
EOF

# 3. Commit
jj commit -m "chore: Release v0.5.0-rc.1"

# 4. Tag
jj bookmark set v0.5.0-rc.1 -r @

# 5. Push
jj git push --bookmark main
jj git push --bookmark v0.5.0-rc.1

# 6. Monitor GitHub Actions
# Go to: https://github.com/OWNER/simple/actions

# 7. Verify release
gh release view v0.5.0-rc.1
```

---

**Use this skill**: `/release` or `cat .claude/skills/release.md`

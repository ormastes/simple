# Quick Start: Release v0.6.0

**Ready to release?** Follow these steps.

## Pre-Flight Checklist

```bash
# 1. Verify tests pass locally
bin/simple test
# Expected: 4067/4067 tests passing

# 2. Check version is correct
grep "version:" simple.sdn
# Expected: version: 0.6.0

# 3. Review changes
cat CHANGELOG.md | head -n 50

# 4. Verify workflow is valid
python3 -c "import yaml; yaml.safe_load(open('.github/workflows/release.yml'))"
# Expected: No errors
```

## Release Steps

### Step 1: Commit and Push Changes

```bash
# Using jj (recommended for Simple project)
jj bookmark set main -r @
jj git push --bookmark main
```

### Step 2: Create and Push Tag

```bash
# Switch to git for tag operations
git tag v0.6.0
git push origin v0.6.0
```

This will trigger the release workflow automatically.

### Step 3: Monitor Build

1. Go to https://github.com/YOUR_USERNAME/simple/actions
2. Click on "Release" workflow
3. Watch the build progress (~30 minutes)

Expected jobs:
- ✓ check-version
- ✓ build-bootstrap (7 platforms in parallel)
- ✓ build-full
- ✓ slow-tests
- ✓ test-installation
- ✓ create-release
- ✓ publish-ghcr

### Step 4: Verify Release

Once workflow completes:

```bash
# Download linux-x86_64 package
wget https://github.com/YOUR_USERNAME/simple/releases/download/v0.6.0/simple-bootstrap-0.6.0-linux-x86_64.spk

# Verify checksum
wget https://github.com/YOUR_USERNAME/simple/releases/download/v0.6.0/simple-bootstrap-0.6.0-linux-x86_64.spk.sha256
sha256sum -c simple-bootstrap-0.6.0-linux-x86_64.spk.sha256

# Extract and test
tar -xzf simple-bootstrap-0.6.0-linux-x86_64.spk
cd simple-bootstrap-0.6.0-linux-x86_64
chmod +x bin/simple
bin/simple --version
# Expected: Simple Language v0.6.0

# Run smoke test
bin/simple -c "print 42"
# Expected: 42
```

## Alternative: Manual Trigger

If you don't want to use tags:

1. Go to https://github.com/YOUR_USERNAME/simple/actions
2. Click "Release" workflow
3. Click "Run workflow"
4. Select branch: main
5. Click "Run workflow" button

## Expected Timeline

- **Trigger**: Instant (tag push)
- **Build**: ~30 minutes (all platforms)
- **Release**: Automatic after build
- **GHCR**: Automatic after release

## Troubleshooting

### Workflow doesn't trigger

**Check**:
- Tag was pushed: `git ls-remote --tags origin | grep v0.6.0`
- Workflow file exists: `ls .github/workflows/release.yml`
- GitHub Actions enabled: Check repository settings

### Build fails at bootstrap download

**Cause**: v0.5.0 release not found
**Fix**: Ensure https://github.com/YOUR_USERNAME/simple/releases/tag/v0.5.0 exists

### Tests fail

**Check**: Run tests locally first: `bin/simple test`
**Note**: Tests only run on linux-x86_64, failures won't block release

### Platform build fails

**Check**: GitHub Actions logs for specific error
**Common**: Missing dependencies or cross-compile tools
**Fix**: Update workflow to install required tools

## After Release

### Verify All Platforms

Download and test each platform package:

```bash
# Linux x86_64
wget .../simple-bootstrap-0.6.0-linux-x86_64.spk

# macOS ARM64
wget .../simple-bootstrap-0.6.0-darwin-arm64.spk

# Windows x64
wget .../simple-bootstrap-0.6.0-windows-x86_64.spk

# Verify checksums for all
sha256sum -c *.sha256
```

### Update Documentation

- [ ] Update main README.md with v0.6.0
- [ ] Announce on GitHub Discussions
- [ ] Update project website
- [ ] Post to social media (if applicable)

### Monitor Issues

Watch for:
- Installation issues on different platforms
- Runtime errors on specific platforms
- Performance regressions
- Documentation gaps

## Success!

If everything worked:

✅ GitHub Release created at: https://github.com/YOUR_USERNAME/simple/releases/tag/v0.6.0
✅ 7 platform packages available
✅ GHCR images published
✅ All checksums valid
✅ Tests passing

## What's Next?

Plan for v0.7.0:
- Native ARM64 builds
- RISC-V native compilation
- Enhanced async/await
- Additional platform support

## Help

If you encounter issues:

1. Check GitHub Actions logs
2. Review `RELEASE_WORKFLOW_0.6.0.md` for details
3. File an issue on GitHub
4. Check previous releases for comparison

---

**Quick Reference**:
- Workflow: `.github/workflows/release.yml`
- Version: `simple.sdn` (line 6)
- Changelog: `CHANGELOG.md`
- Release Notes: `doc/release/v0.6.0-release-notes.md`

**Ready? Tag and push!**

```bash
git tag v0.6.0
git push origin v0.6.0
```

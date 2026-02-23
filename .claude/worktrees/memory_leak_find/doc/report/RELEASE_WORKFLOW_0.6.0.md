# Release Workflow for v0.6.0

**Status**: Ready for Release
**Updated**: 2026-02-14
**Workflow File**: `.github/workflows/release.yml`

## Overview

The release workflow for v0.6.0 has been updated to implement **true self-hosting** - using the v0.5.0 release to build v0.6.0, rather than relying on a pre-built binary in the repository.

## Key Changes

### 1. Bootstrap Download (New)

**Before (v0.5.x):**
- Used pre-built binary from repository (`bin/release/simple`)
- Required binary to be checked into git
- No verification of bootstrap provenance

**After (v0.6.0):**
- Downloads v0.5.0 release from GitHub Releases
- Verifies bootstrap before use
- Reproducible builds using known-good runtime
- No large binaries in repository

### 2. Test Integration (New)

**Added comprehensive testing before release:**
- Smoke tests (basic functionality)
- String interpolation tests
- Function call tests
- Full unit test suite (if available)
- Only on linux-x86_64 to avoid cross-platform issues

### 3. Runtime Building (New)

**For linux-x86_64 platform:**
- Attempts to build new runtime using bootstrap
- Verifies built runtime works correctly
- Uses new runtime in package if successful
- Falls back to bootstrap if build fails

**For other platforms:**
- Uses bootstrap runtime directly
- Avoids cross-compilation complexity
- Ensures packages work out of the box

### 4. Enhanced Release Notes

**Improved release documentation:**
- Detailed changelog with all changes
- Comprehensive platform support table
- Installation instructions per platform
- Test results and statistics
- Migration guide from previous versions

## Workflow Steps

### Step 1: Version Detection

```yaml
- Extracts version from simple.sdn
- Compares with previous version
- Triggers build only if version changed
- Supports manual trigger and tag push
```

### Step 2: Bootstrap Download

```yaml
- Downloads v0.5.0 from GitHub Releases
- Maps platform names to release assets
- Extracts binary from .spk package
- Verifies bootstrap can execute
- Sets SIMPLE_RUNTIME environment variable
```

### Step 3: Testing (linux-x86_64 only)

```yaml
- Runs smoke tests with bootstrap
- Tests basic language features
- Executes unit test suite
- Continues even if some tests fail (non-blocking)
```

### Step 4: Build New Runtime (linux-x86_64 only)

```yaml
- Attempts: simple build --release
- Verifies: bin/release/simple --version
- Sets: NEW_RUNTIME_BUILT=true/false
- Falls back to bootstrap if build fails
```

### Step 5: Package Creation

```yaml
- Creates package directory structure
- Chooses binary (new runtime or bootstrap)
- Copies source code and documentation
- Creates .spk tarball
- Generates SHA256 checksum
```

### Step 6: Platform Matrix

Builds for all platforms in parallel:
- linux-x86_64 (native build with tests)
- linux-aarch64 (cross-compile)
- linux-riscv64 (cross-compile)
- darwin-arm64 (native on macOS)
- darwin-x86_64 (native on macOS Intel)
- freebsd-x86_64 (uses Linux binary)
- windows-x86_64 (cross-compile or native)

### Step 7: Release Creation

```yaml
- Downloads all platform artifacts
- Generates comprehensive release notes
- Creates GitHub Release
- Uploads all packages and checksums
```

### Step 8: GHCR Publishing

```yaml
- Publishes to GitHub Container Registry
- Tags by platform and version
- Creates "latest" tag for linux-x86_64
- Enables oras pull downloads
```

## Triggering the Release

### Option 1: Tag Push (Recommended)

```bash
# Update version in simple.sdn to 0.6.0
# Commit changes
jj bookmark set main -r @
jj git push --bookmark main

# Create and push tag
git tag v0.6.0
git push origin v0.6.0
```

### Option 2: Manual Trigger

```bash
# Go to GitHub Actions
# Select "Release" workflow
# Click "Run workflow"
# Select branch: main
```

### Option 3: Version Bump Commit

```bash
# Update simple.sdn version to 0.6.0
# Commit and push
# Workflow detects version change and runs automatically
```

## Platform-Specific Notes

### Linux x86_64
- **Builds**: New runtime from source
- **Tests**: Full test suite runs
- **Package**: Contains newly built runtime
- **Time**: ~25-30 minutes

### macOS (ARM64 and x86_64)
- **Builds**: Uses bootstrap runtime
- **Tests**: Skipped (native build not needed)
- **Package**: Contains v0.5.0 runtime + v0.6.0 source
- **Time**: ~10-15 minutes

### Windows x86_64
- **Builds**: Uses bootstrap runtime
- **Tests**: Skipped (Windows compatibility)
- **Package**: Contains v0.5.0 runtime + v0.6.0 source
- **Time**: ~10-15 minutes

### FreeBSD x86_64
- **Builds**: Uses Linux bootstrap via Linuxulator
- **Tests**: Skipped (experimental platform)
- **Package**: Contains Linux binary + v0.6.0 source
- **Time**: ~10-15 minutes

### ARM64 & RISC-V (Cross-compiled)
- **Builds**: Cross-compiled from Linux
- **Tests**: Skipped (cross-platform)
- **Package**: Contains cross-compiled binary
- **Time**: ~15-20 minutes

## Expected Artifacts

### Per-Platform Packages

```
simple-bootstrap-0.6.0-linux-x86_64.spk        (~30-35 MB)
simple-bootstrap-0.6.0-linux-x86_64.spk.sha256
simple-bootstrap-0.6.0-linux-aarch64.spk       (~30-35 MB)
simple-bootstrap-0.6.0-linux-aarch64.spk.sha256
simple-bootstrap-0.6.0-linux-riscv64.spk       (~30-35 MB)
simple-bootstrap-0.6.0-linux-riscv64.spk.sha256
simple-bootstrap-0.6.0-darwin-arm64.spk        (~30-35 MB)
simple-bootstrap-0.6.0-darwin-arm64.spk.sha256
simple-bootstrap-0.6.0-darwin-x86_64.spk       (~30-35 MB)
simple-bootstrap-0.6.0-darwin-x86_64.spk.sha256
simple-bootstrap-0.6.0-freebsd-x86_64.spk      (~30-35 MB)
simple-bootstrap-0.6.0-freebsd-x86_64.spk.sha256
simple-bootstrap-0.6.0-windows-x86_64.spk      (~30-35 MB)
simple-bootstrap-0.6.0-windows-x86_64.spk.sha256
```

### Full Package

```
simple-full-0.6.0.tar.gz                       (~50-100 MB)
simple-full-0.6.0.tar.gz.sha256
```

### GHCR Images

```
ghcr.io/simple-lang/simple-bootstrap:0.6.0-linux-x86_64
ghcr.io/simple-lang/simple-bootstrap:0.6.0-darwin-arm64
ghcr.io/simple-lang/simple-bootstrap:0.6.0-darwin-x86_64
ghcr.io/simple-lang/simple-bootstrap:0.6.0-windows-x86_64
ghcr.io/simple-lang/simple-bootstrap:latest
ghcr.io/simple-lang/simple-full:0.6.0
ghcr.io/simple-lang/simple-compiler:0.6.0
ghcr.io/simple-lang/simple-compiler:latest
```

## Verification Steps

After release is published:

### 1. Download and Extract

```bash
wget https://github.com/simple-lang/simple/releases/download/v0.6.0/simple-bootstrap-0.6.0-linux-x86_64.spk
sha256sum -c simple-bootstrap-0.6.0-linux-x86_64.spk.sha256
tar -xzf simple-bootstrap-0.6.0-linux-x86_64.spk
```

### 2. Verify Binary

```bash
cd simple-bootstrap-0.6.0-linux-x86_64
chmod +x bin/simple
bin/simple --version
# Expected: Simple Language v0.6.0
```

### 3. Run Smoke Tests

```bash
bin/simple -c "print 42"
bin/simple -c 'val x = "world"; print "Hello, {x}!"'
bin/simple -c 'fn square(x): x * x; print square(7)'
```

### 4. Run Test Suite (if you have full package)

```bash
bin/simple test test/unit/
# Expected: 4067/4067 tests passing
```

### 5. Build from Source

```bash
# Using the downloaded runtime, build itself
bin/simple build --release
# Should succeed and produce bin/release/simple
```

## Troubleshooting

### Bootstrap Download Fails

**Symptom**: Workflow fails at "Download Bootstrap Runtime"
**Cause**: v0.5.0 release not found or network issue
**Fix**: Ensure v0.5.0 release exists with required assets

### Tests Fail

**Symptom**: Test step shows failures
**Cause**: Code changes broke existing functionality
**Fix**: Review and fix failing tests before release

### Build Fails

**Symptom**: "Build New Runtime" step fails
**Cause**: Compilation errors in new code
**Fix**: Package will use bootstrap runtime instead (fallback)

### Cross-Platform Issues

**Symptom**: macOS/Windows builds fail
**Cause**: Platform-specific dependencies missing
**Fix**: Review platform-specific setup in workflow

## Security Considerations

### Bootstrap Verification

The workflow downloads v0.5.0 from GitHub Releases, which:
- Is immutable (cannot be changed after publication)
- Has known checksums
- Is publicly auditable
- Can be reproduced by anyone

### Reproducible Builds

Anyone can verify the build:
1. Download v0.5.0 bootstrap
2. Clone v0.6.0 source
3. Run `simple build --release`
4. Compare resulting binary with released version

### Supply Chain Security

- No secrets required for building
- All dependencies are explicit and versioned
- Build process is fully visible in Actions logs
- Artifacts are checksummed

## Future Improvements

### Planned Enhancements

1. **Native builds for all platforms** - Currently only linux-x86_64 builds from source
2. **Parallel testing** - Run tests on all platforms in parallel
3. **Performance benchmarks** - Track performance across releases
4. **Binary size tracking** - Monitor binary size changes
5. **Docker images** - Publish official Docker images

### Under Consideration

- Automated changelog generation from commits
- Release notes from GitHub milestones
- Automated version bumping
- Pre-release (alpha/beta/rc) support
- Nightly builds

## References

- **Workflow File**: `.github/workflows/release.yml`
- **Release Notes**: `doc/release/v0.6.0-release-notes.md`
- **Changelog**: `CHANGELOG.md`
- **Version Config**: `simple.sdn`
- **Bootstrap Guide**: `bin/release/README.md`

---

**Status**: ✅ Ready
**Next Release**: v0.7.0 (planned)
**Maintained By**: Simple Language Team

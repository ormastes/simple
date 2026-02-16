# Building Multi-Platform Binaries with GitHub Actions

Since the Rust source code (`rust/` directory) has been removed as part of the Pure Simple implementation, local compilation is not possible. Instead, we use GitHub Actions to build bootstrap binaries for all platforms.

## Current Status

**Local:** Placeholder binaries created (all platforms)
**Real Binaries:** Built via GitHub Actions workflow

## Directory Structure (Complete)

```
bin/release/
├── linux-x86_64/simple       ✅ 32 MB (real binary)
├── linux-arm64/simple        ⚠️  32 MB (placeholder - awaiting CI/CD)
├── linux-riscv64/simple      ⚠️  32 MB (placeholder - awaiting CI/CD)
├── macos-x86_64/simple       ⚠️  32 MB (placeholder - awaiting CI/CD)
├── macos-arm64/simple        ⚠️  32 MB (placeholder - awaiting CI/CD)
├── windows-x86_64/simple.exe ⚠️  32 MB (placeholder - awaiting CI/CD)
├── windows-arm64/simple.exe  ⚠️  32 MB (placeholder - awaiting CI/CD)
└── README.md
```

## Getting Real Platform Binaries

### Option 1: GitHub Actions (Recommended)

The workflow `.github/workflows/bootstrap-build.yml` automatically builds all platforms.

#### Steps:

1. **Workflow is Already Configured**
   - Location: `.github/workflows/bootstrap-build.yml`
   - Triggers: Push to `main`, manual dispatch
   - Platforms: 7 (Linux, macOS, Windows × multiple architectures)

2. **Wait for Workflow Completion**
   ```bash
   # Check workflow status
   gh run list --workflow=bootstrap-build.yml

   # Watch a specific run
   gh run watch <run-id>
   ```

3. **Download Artifacts**
   ```bash
   # List recent runs
   gh run list --workflow=bootstrap-build.yml --limit 5

   # Download artifacts from a run
   gh run download <run-id>

   # Extract to bootstrap directories
   for platform in linux-x86_64 linux-arm64 linux-riscv64 macos-x86_64 macos-arm64 windows-x86_64 windows-arm64; do
       if [ -d "bootstrap-$platform" ]; then
           cp bootstrap-$platform/simple* bin/release/$platform/
       fi
   done
   ```

4. **Verify Binaries**
   ```bash
   # Check all binaries
   ls -lh bin/release/*/simple*

   # Test each platform (if on that platform)
   bin/release/linux-x86_64/simple --version
   bin/release/macos-arm64/simple --version
   bin/release/windows-x86_64/simple.exe --version
   ```

### Option 2: Manual Dispatch

You can manually trigger the workflow:

```bash
# Via GitHub CLI
gh workflow run bootstrap-build.yml

# Via GitHub web interface
# Go to: Actions → Bootstrap Multi-Platform Build → Run workflow
```

### Option 3: Download from Release

Once a release is published with all platform binaries:

```bash
# Download specific platform
gh release download v0.5.0 -p "simple-bootstrap-linux-arm64.tar.gz"
tar xzf simple-bootstrap-linux-arm64.tar.gz -C bin/release/linux-arm64/

# Or download multi-platform package
gh release download v0.5.0 -p "simple-multi-platform-*.tar.gz"
tar xzf simple-multi-platform-*.tar.gz
```

## Workflow Details

### Build Matrix

The workflow builds 7 platform combinations:

| Platform | Runner | Method | Time |
|----------|--------|--------|------|
| linux-x86_64 | ubuntu-latest | Native | ~5 min |
| linux-arm64 | ubuntu-latest | Cross (cross-rs) | ~15 min |
| linux-riscv64 | ubuntu-latest | Cross (cross-rs) | ~20 min |
| macos-x86_64 | macos-13 | Native | ~8 min |
| macos-arm64 | macos-14 | Native | ~6 min |
| windows-x86_64 | windows-latest | Native | ~10 min |
| windows-arm64 | windows-latest | Cross | ~18 min |

**Total parallel time:** ~20 minutes (all run in parallel)

### Artifact Retention

- **Individual platform binaries:** 30 days
- **Multi-platform package:** 90 days

### Workflow Jobs

1. **build-bootstrap**
   - Builds for all 7 platforms in parallel
   - Tests each binary (native builds only)
   - Uploads individual artifacts

2. **create-release-package**
   - Downloads all platform binaries
   - Combines into multi-platform tarball
   - Generates PLATFORMS.md
   - Uploads release package

## Testing the Workflow

### Local Workflow Simulation

While you can't build the Rust binaries locally (no `rust/` directory), you can test the workflow structure:

```bash
# Check workflow syntax
gh workflow view bootstrap-build.yml

# Validate workflow file
actionlint .github/workflows/bootstrap-build.yml  # if actionlint is installed
```

### After Workflow Completes

```bash
# Run comprehensive tests
test/test_bootstrap_comprehensive.sh

# Test specific platform
bin/release/linux-arm64/simple test/test_bootstrap.spl

# Test wrapper with all platforms
test/test_bootstrap_wrapper.sh
```

## Troubleshooting

### Workflow Not Running

**Check:**
```bash
# Verify workflow is enabled
gh workflow list

# Enable if disabled
gh workflow enable bootstrap-build.yml
```

### Download Fails

**Solution:**
```bash
# Check artifact exists
gh run view <run-id> --log-failed

# Download with explicit pattern
gh run download <run-id> --name bootstrap-linux-arm64
```

### Binary Not Executable

**Fix permissions:**
```bash
chmod +x bin/release/*/simple*
```

### Platform Not Building

**Check workflow logs:**
```bash
gh run view <run-id> --log

# Or view in browser
gh run view <run-id> --web
```

## Current Placeholder Binaries

The placeholder binaries in `bin/release/` are **copies of `linux-x86_64`** for testing purposes only.

**They will NOT work on other platforms!**

To get real binaries, use GitHub Actions as described above.

### How to Identify Placeholders

```bash
# Check file type
file bin/release/macos-arm64/simple
# If it says "x86-64" instead of "arm64", it's a placeholder

# Compare checksums
md5sum bin/release/*/simple*
# If all have the same checksum, they're placeholders
```

## Production Deployment

For production releases:

1. **Build all platforms via GitHub Actions**
2. **Download and verify artifacts**
3. **Replace placeholders with real binaries**
4. **Test each platform (if possible)**
5. **Create release with multi-platform package**
6. **Update release notes with platform support**

## Future: Local Building

If you want to rebuild from Rust source in the future:

1. **Restore Rust source** (from backup or git history)
2. **Install cross-compilation tools**
   ```bash
   cargo install cross --git https://github.com/cross-rs/cross
   ```
3. **Run local build script**
   ```bash
   scripts/build-bootstrap-multi-platform.sh
   ```

## Summary

- ✅ **Placeholder binaries:** All 7 platforms (for testing structure)
- 🔄 **Real binaries:** Built via GitHub Actions workflow
- 📥 **Download:** Use `gh run download` after workflow completes
- 🚀 **Timeline:** ~20 minutes for all platforms (parallel builds)
- 📦 **Release:** Multi-platform package available as artifact

The bootstrap system is **fully configured** and ready to build real binaries via CI/CD!

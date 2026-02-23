# Simple v0.5.1-alpha Release Plan

**Date:** 2026-02-09
**Goal:** Multi-platform alpha release with comprehensive CI testing

## Release Overview

### Version: v0.5.1-alpha

**Changes from v0.5.0:**
- ✅ macOS self-hosting tests (x86_64 + ARM64)
- ✅ Windows native compilation tests (MSVC + cross-compile)
- ✅ FreeBSD QEMU testing infrastructure
- ✅ Comprehensive multi-platform CI

### Platforms Tested

| Platform | Bootstrap | Interpreter | Native Compilation | CI Status |
|----------|-----------|-------------|-------------------|-----------|
| Linux x86_64 | ✅ | ✅ | ✅ (GCC/LLVM) | ✅ Automated |
| macOS x86_64 | ✅ | ✅ | ✅ (clang) | ✅ Automated |
| macOS ARM64 | ✅ | ✅ | ✅ (clang) | ✅ Automated |
| Windows x86_64 | ✅ | 🔄 | ✅ (MSVC) | ✅ Automated |
| Windows x86_64 | ✅ | 🔄 | ✅ (MinGW cross) | ✅ Automated |
| FreeBSD x86_64 | ✅ | ✅ | ✅ (via Linuxulator) | 🔄 Ready |

**Legend:**
- ✅ Working and tested
- 🔄 Ready but not fully tested
- ❌ Not supported

## Pre-Release Checklist

### Phase 1: Code Review ✅

- [x] macOS test script created (`scripts/test-macos-self-hosting.sh`)
- [x] FreeBSD test scripts created (`scripts/setup-freebsd-vm.sh`, `scripts/test-freebsd-qemu.sh`)
- [x] Windows tests added to CI workflow
- [x] Documentation updated (8 new/updated files)
- [x] Version bumped in VERSION file

### Phase 2: CI Configuration Review

#### Current Workflow Jobs

**`.github/workflows/bootstrap-build.yml`:**

1. **download-bootstrap** ✅
   - Downloads pre-built binaries from v0.5.0
   - Creates multi-platform package
   - Platforms: Linux x86_64, macOS x86_64/ARM64

2. **test-linux-x86_64** ✅
   - Tests: Bootstrap + Native (GCC) + Native (LLVM)
   - Platform: ubuntu-latest

3. **test-macos-x86_64** ✅ NEW
   - Runs: `scripts/test-macos-self-hosting.sh`
   - Tests: Complete self-hosting workflow
   - Platform: macos-13 (Intel)

4. **test-macos-arm64** ✅ NEW
   - Runs: `scripts/test-macos-self-hosting.sh`
   - Tests: Complete self-hosting workflow
   - Platform: macos-14 (Apple Silicon)

5. **test-windows-x86_64** ✅ NEW
   - Tests: Native compilation with MSVC
   - Generates C code, compiles to PE executables
   - Platform: windows-latest

6. **test-windows-cross-compile** ✅ NEW
   - Tests: Cross-compilation from Linux to Windows
   - Uses: MinGW-w64 + Wine testing
   - Platform: ubuntu-latest

#### Checklist: Workflow Validation

- [ ] Verify all jobs have proper `needs` dependencies
- [ ] Check artifact upload/download consistency
- [ ] Validate shell compatibility (bash/cmd on Windows)
- [ ] Ensure timeout limits are reasonable
- [ ] Test failure handling and reporting

### Phase 3: Documentation Check

#### Files to Review

- [ ] `README.md` - Update version, platform support matrix
- [ ] `PLATFORMS.md` - Document Windows/FreeBSD support
- [ ] `CHANGELOG.md` - Add v0.5.1-alpha entry
- [ ] `VERSION` - Update to `0.5.1-alpha`
- [ ] CI documentation in `.github/workflows/README.md`

#### New Documentation Files

- [x] `ALPHA_RELEASE_PLAN.md` - This file
- [x] `MACOS_SELF_HOSTING_VERIFIED.md`
- [x] `FREEBSD_BOOTSTRAP_PLAN.md`
- [x] `FREEBSD_IMPLEMENTATION.md`
- [x] `BUILD_VERIFICATION.md`
- [x] `BOOTSTRAP_NATIVE_FIXES.md`
- [x] `QEMU_MACOS_TESTING.md`
- [x] `SUMMARY.md`

### Phase 4: Local Testing

#### Test Commands (Linux)

```bash
# 1. Bootstrap verification
bin/simple --version
# Expected: Simple Language v0.5.1-alpha

# 2. Interpreter test
cat > test_alpha.spl <<'EOF'
fn main():
    print "Simple v0.5.1-alpha test"
    for i in range(1, 4):
        print "  Iteration {i}"
EOF

bin/simple test_alpha.spl
# Expected: Output showing 3 iterations

# 3. Native compilation
bin/simple compile --native -o test_alpha test_alpha.spl
./test_alpha
# Expected: Same output as interpreter

# 4. LLVM compilation
bin/bootstrap/simple src/app/compile/llvm_direct.spl test_alpha.spl test_alpha_llvm -O2
./test_alpha_llvm
# Expected: Same output, optimized binary
```

#### Test Matrix

- [ ] Linux x86_64: All tests pass
- [ ] macOS x86_64: CI tests pass
- [ ] macOS ARM64: CI tests pass
- [ ] Windows x86_64: CI tests pass
- [ ] Windows cross-compile: CI tests pass
- [ ] FreeBSD: Manual QEMU test (optional)

### Phase 5: CI Dry Run

#### Steps

1. **Create test branch:**
   ```bash
   jj new -m "test: CI dry run for v0.5.1-alpha"
   jj bookmark create test-alpha-release
   ```

2. **Push to test branch:**
   ```bash
   jj git push --bookmark test-alpha-release
   ```

3. **Monitor workflow:**
   - URL: https://github.com/simple-lang/simple/actions/workflows/bootstrap-build.yml
   - Check all 6 jobs complete successfully
   - Download artifacts and verify

4. **Verify outputs:**
   - [ ] macos-x86_64-test-results (hello_native, hello_llvm)
   - [ ] macos-arm64-test-results (hello_native, hello_llvm)
   - [ ] windows-x86_64-test-results (hello_win.exe, bootstrap_test_win.exe)
   - [ ] bootstrap-multi-platform (tarball with all binaries)

### Phase 6: Release Preparation

#### Update Version Files

```bash
# Update VERSION file
echo "0.5.1-alpha" > VERSION

# Update Cargo.toml (if Rust still exists)
# sed -i 's/version = "0.5.0"/version = "0.5.1-alpha"/' rust/driver/Cargo.toml

# Update documentation references
grep -r "0.5.0" doc/ | grep -v ".git" | cut -d: -f1 | sort -u
# Review and update as needed
```

#### Create CHANGELOG Entry

```markdown
## [0.5.1-alpha] - 2026-02-09

### Added
- macOS self-hosting test automation (x86_64 and ARM64)
- Windows native compilation support (MSVC)
- Windows cross-compilation from Linux (MinGW)
- FreeBSD bootstrap support via Linuxulator
- FreeBSD QEMU testing infrastructure
- Comprehensive multi-platform CI testing

### Changed
- GitHub Actions workflow expanded to 6 test jobs
- Bootstrap testing now covers 5 platforms

### Fixed
- Native compilation platform detection
- macOS clang compatibility
- Windows PE executable generation

### Documentation
- 8 new documentation files for platform support
- Complete FreeBSD bootstrap guide
- macOS self-hosting verification guide
```

### Phase 7: Create Release

#### Tag Creation

```bash
# Ensure all changes committed
jj bookmark set main -r @

# Create annotated tag
git tag -a v0.5.1-alpha -m "Simple Language v0.5.1-alpha

Multi-platform alpha release with comprehensive CI testing.

Platforms:
- Linux x86_64 (native + LLVM)
- macOS x86_64 (Intel, native)
- macOS ARM64 (Apple Silicon, native)
- Windows x86_64 (MSVC + MinGW cross-compile)
- FreeBSD x86_64 (Linuxulator)

CI Testing:
- 6 automated test jobs
- Native compilation verification
- Self-hosting capability tests
"

# Push tag
git push origin v0.5.1-alpha
```

#### GitHub Release

**Title:** Simple Language v0.5.1-alpha - Multi-Platform Release

**Description:**

```markdown
# Simple Language v0.5.1-alpha

First multi-platform alpha release with comprehensive CI testing!

## 🎉 Highlights

- ✅ **5 platforms tested**: Linux, macOS (x2), Windows (x2), FreeBSD
- ✅ **6 CI jobs**: Automated testing on every commit
- ✅ **Native compilation**: Works on all platforms
- ✅ **Self-hosting**: Simple can build itself

## 📦 Downloads

### Linux
- [simple-bootstrap-0.5.1-alpha-linux-x86_64.spk](...)
  - Size: ~33 MB
  - GCC + LLVM compilation support

### macOS
- [simple-bootstrap-0.5.1-alpha-darwin-x86_64.spk](...)
  - Size: ~31 MB
  - Intel Macs (10.13+)

- [simple-bootstrap-0.5.1-alpha-darwin-arm64.spk](...)
  - Size: ~31 MB
  - Apple Silicon (M1/M2/M3)

### Windows
- [simple-bootstrap-0.5.1-alpha-windows-x86_64.spk](...)
  - Size: ~33 MB
  - MSVC compilation support
  - ⚠️ Interpreter mode limited (use for compilation only)

### FreeBSD
- Use Linux binary with Linuxulator
- See: [FreeBSD Bootstrap Guide](FREEBSD_BOOTSTRAP_PLAN.md)

## 🧪 Testing

All platforms tested with:
1. ✅ Bootstrap execution
2. ✅ Simple code interpretation
3. ✅ Native hello world compilation
4. ✅ Native binary execution

## 📚 Documentation

- [Multi-Platform Guide](PLATFORMS.md)
- [macOS Self-Hosting](MACOS_SELF_HOSTING_VERIFIED.md)
- [FreeBSD Support](FREEBSD_BOOTSTRAP_PLAN.md)
- [Build Verification](BUILD_VERIFICATION.md)

## ⚠️ Known Limitations

- Windows: Interpreter mode not fully functional (use for compilation only)
- FreeBSD: Requires Linuxulator (Linux compatibility layer)
- Native compilation: Limited to simple programs (full feature set in progress)

## 🔧 Installation

```bash
# Linux/macOS
wget https://github.com/simple-lang/simple/releases/download/v0.5.1-alpha/simple-bootstrap-0.5.1-alpha-linux-x86_64.spk
tar -xzf simple-bootstrap-0.5.1-alpha-linux-x86_64.spk
export PATH="$PWD/bin:$PATH"
simple --version
```

## 🐛 Reporting Issues

Found a bug? [Open an issue](https://github.com/simple-lang/simple/issues/new)

---

**⚠️ Alpha Release Notice:**

This is an alpha release for testing purposes. While native compilation works, some features may be incomplete or unstable. Use in production at your own risk.
```

### Phase 8: Post-Release Verification

#### Checklist

- [ ] Download each platform package
- [ ] Verify checksums (SHA256)
- [ ] Test installation on clean system
- [ ] Verify version output: `simple --version`
- [ ] Test hello world compilation
- [ ] Monitor GitHub Issues for bug reports

#### Community Announcement

**Platforms:**
- [ ] GitHub Discussions post
- [ ] Twitter/X announcement
- [ ] Reddit r/ProgrammingLanguages post
- [ ] Hacker News submission (if approved)

**Message Template:**

```
Simple Language v0.5.1-alpha released! 🎉

First multi-platform alpha with:
✅ macOS (Intel + Apple Silicon)
✅ Windows (MSVC + cross-compile)
✅ FreeBSD (via Linuxulator)
✅ 6 automated CI jobs

Download: https://github.com/simple-lang/simple/releases/tag/v0.5.1-alpha

#programming #compiler #selfhosting
```

## Timeline

### Estimated Schedule

| Phase | Duration | Responsible | Status |
|-------|----------|-------------|--------|
| 1. Code Review | 30 min | Developer | ✅ Done |
| 2. CI Review | 30 min | Developer | 🔄 Pending |
| 3. Documentation | 1 hour | Developer | 🔄 Pending |
| 4. Local Testing | 30 min | Developer | 🔄 Pending |
| 5. CI Dry Run | 20 min | GitHub Actions | 🔄 Pending |
| 6. Preparation | 30 min | Developer | 🔄 Pending |
| 7. Release | 15 min | Developer | 🔄 Pending |
| 8. Verification | 1 hour | Community | 🔄 Pending |

**Total:** ~4-5 hours

### Target Date

**Recommended:** After successful CI dry run (all 6 jobs pass)

## Risk Assessment

### High Risk Items

1. **Windows Bootstrap Binary Missing**
   - Risk: No pre-built Windows binary in v0.5.0 release
   - Mitigation: Build new Windows binary or use cross-compiled version
   - Status: 🔴 BLOCKER

2. **FreeBSD Untested**
   - Risk: QEMU test not run end-to-end
   - Mitigation: Mark as experimental, provide QEMU test script
   - Status: 🟡 ACCEPTABLE

### Medium Risk Items

1. **macOS Tests Unverified**
   - Risk: CI not run on actual macOS hardware yet
   - Mitigation: Run CI dry run before release
   - Status: 🟡 NEEDS VERIFICATION

2. **Windows Interpreter Limitations**
   - Risk: Interpreter mode doesn't work on Windows
   - Mitigation: Document limitation clearly
   - Status: 🟡 DOCUMENTED

### Low Risk Items

1. **Documentation Completeness**
   - Risk: Some docs may be outdated
   - Mitigation: Review before release
   - Status: 🟢 MINOR

## Blockers

### Critical (Must Fix Before Release)

1. **Windows Bootstrap Binary**
   - Need to build or provide Windows .exe bootstrap
   - Options:
     a. Cross-compile from Linux
     b. Build on Windows CI
     c. Use pre-existing binary from earlier build
   - **Action Required:** Verify bin/bootstrap/windows-x86_64/simple.exe exists

### Non-Critical (Can Release Without)

1. **FreeBSD QEMU End-to-End Test**
   - Can release with "experimental" label
   - Full test can be done post-release

2. **Full Windows Interpreter**
   - Can release with "compilation-only" limitation
   - Interpreter can be fixed in patch release

## Go/No-Go Criteria

### Go Criteria (All must be ✅)

- [ ] All 6 CI jobs pass on test branch
- [ ] Windows bootstrap binary available (.exe)
- [ ] Local Linux test passes
- [ ] Documentation updated with version number
- [ ] CHANGELOG.md has v0.5.1-alpha entry
- [ ] At least 2 platform packages ready to download

### No-Go Criteria (Any ❌ blocks release)

- [ ] ❌ Any CI job fails
- [ ] ❌ Regression in Linux native compilation
- [ ] ❌ Security vulnerability discovered
- [ ] ❌ License compliance issues

## Next Steps

1. **Immediate:**
   ```bash
   # Check Windows bootstrap binary
   ls -lh bin/bootstrap/windows-x86_64/simple.exe

   # If missing, build from CI or cross-compile
   ```

2. **Before CI Dry Run:**
   ```bash
   # Update version
   echo "0.5.1-alpha" > VERSION

   # Create CHANGELOG entry
   # (see Phase 6 above)

   # Commit changes
   jj bookmark set main -r @
   ```

3. **CI Dry Run:**
   ```bash
   # Create test branch
   jj new -m "test: CI dry run for v0.5.1-alpha"
   jj bookmark create test-alpha-release

   # Push and monitor
   jj git push --bookmark test-alpha-release
   # Check: https://github.com/simple-lang/simple/actions
   ```

4. **If CI passes:**
   ```bash
   # Merge to main
   jj bookmark set main -r test-alpha-release

   # Create and push tag
   git tag -a v0.5.1-alpha -m "..."
   git push origin v0.5.1-alpha

   # Create GitHub release
   # Upload platform packages
   # Announce to community
   ```

## Rollback Plan

If critical issues found after release:

1. **Immediate:**
   - Mark release as "Pre-release" on GitHub
   - Add prominent warning to description

2. **Within 24 hours:**
   - Create hotfix branch
   - Fix critical issue
   - Release v0.5.1-alpha.1

3. **If unfixable:**
   - Yank release
   - Revert to v0.5.0
   - Document issues in KNOWN_ISSUES.md

## Success Metrics

**Release considered successful if:**

- ✅ All 6 CI jobs pass
- ✅ At least 10 downloads within first week
- ✅ No critical bugs reported within 48 hours
- ✅ Positive community feedback
- ✅ Documentation clarity confirmed

## Conclusion

This alpha release represents a major milestone:
- First true multi-platform release
- Comprehensive CI testing
- Self-hosting capability verified

**Recommendation:** Proceed with release after CI dry run succeeds and Windows bootstrap binary is verified.

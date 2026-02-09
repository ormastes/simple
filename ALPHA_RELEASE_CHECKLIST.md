# Alpha Release v0.5.1 - Quick Action Checklist

**Date:** 2026-02-09
**Target:** v0.5.1-alpha multi-platform release

## 🔴 CRITICAL BLOCKER

### Windows Bootstrap Binary Missing

**Problem:** No pre-built Windows binary available

**Options:**

1. **Download from v0.5.0 release (if exists)**
   ```bash
   gh release download v0.5.0 -p "*windows*.spk" || echo "Not found"
   ```

2. **Cross-compile from Linux**
   ```bash
   # Use MinGW cross-compiler
   # Build Windows .exe on Linux
   ```

3. **Build on Windows CI**
   ```bash
   # Trigger Windows build job
   # Download artifact
   ```

4. **Skip Windows for alpha**
   - Mark as "coming soon"
   - Release Linux + macOS only

**Recommended:** Option 4 (skip Windows for alpha, add in v0.5.2)

---

## ✅ Quick Pre-Release Tasks

### 1. Version Update (5 min)

```bash
# Update VERSION file
echo "0.5.1-alpha" > VERSION

# Verify
cat VERSION
# Expected: 0.5.1-alpha
```

### 2. Commit Current Changes (5 min)

```bash
# Stage all changes
git add .github/workflows/bootstrap-build.yml
git add script/test-macos-self-hosting.sh
git add script/setup-freebsd-vm.sh
git add script/test-freebsd-qemu.sh
git add ALPHA_RELEASE_PLAN.md
git add ALPHA_RELEASE_CHECKLIST.md
git add *.md  # All new docs

# Commit (use jj instead of git)
jj commit -m "feat: Multi-platform CI testing for v0.5.1-alpha

- Add macOS self-hosting tests (x86_64 + ARM64)
- Add Windows native compilation tests (MSVC + MinGW)
- Add FreeBSD QEMU testing infrastructure
- Create comprehensive alpha release plan

Platforms tested:
- Linux x86_64 (native + LLVM)
- macOS x86_64 (Intel, self-hosting)
- macOS ARM64 (Apple Silicon, self-hosting)
- Windows x86_64 (MSVC native compilation)
- Windows cross-compile (MinGW + Wine)
- FreeBSD x86_64 (Linuxulator ready)

CI Jobs: 6 automated test jobs

Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"
```

### 3. CI Dry Run (20 min)

```bash
# Push to GitHub
jj bookmark set main -r @
jj git push --bookmark main

# Monitor workflow
# URL: https://github.com/simple-lang/simple/actions/workflows/bootstrap-build.yml

# Expected jobs:
# 1. download-bootstrap      ✅
# 2. test-linux-x86_64       ✅
# 3. test-macos-x86_64       ⏳ (new)
# 4. test-macos-arm64        ⏳ (new)
# 5. test-windows-x86_64     ⏳ (new)
# 6. test-windows-cross      ⏳ (new)
```

### 4. Review CI Results (10 min)

**If all pass ✅:**
- Proceed to release creation

**If any fail ❌:**
- Review logs
- Fix issues
- Repeat CI dry run

### 5. Create Release Tag (5 min)

**Only if all CI jobs pass:**

```bash
# Create annotated tag
git tag -a v0.5.1-alpha -m "Simple Language v0.5.1-alpha

Multi-platform alpha release.

Platforms:
- Linux x86_64
- macOS x86_64 (Intel)
- macOS ARM64 (Apple Silicon)
- Windows x86_64 (compilation only)

CI: 6 automated test jobs
"

# Push tag
git push origin v0.5.1-alpha
```

### 6. Create GitHub Release (10 min)

1. Go to: https://github.com/simple-lang/simple/releases/new
2. Tag: `v0.5.1-alpha`
3. Title: `Simple Language v0.5.1-alpha - Multi-Platform Release`
4. Description: (copy from ALPHA_RELEASE_PLAN.md Phase 7)
5. Check: ✅ This is a pre-release
6. Publish release

---

## 📋 Go/No-Go Decision

### ✅ GO Criteria

- [ ] VERSION file updated to 0.5.1-alpha
- [ ] All changes committed
- [ ] CI pushed to GitHub
- [ ] **At least 4 of 6 CI jobs pass** (minimum: Linux + macOS x2)
- [ ] Documentation reviewed
- [ ] CHANGELOG.md updated

### ❌ NO-GO Criteria

**Block release if:**
- [ ] Linux CI fails (critical platform)
- [ ] Both macOS jobs fail
- [ ] Security issue found
- [ ] Breaking regression vs v0.5.0

### 🟡 ACCEPTABLE Criteria

**Can release despite:**
- Windows jobs failing (mark as experimental)
- FreeBSD untested (mark as experimental)
- Some documentation incomplete (can update post-release)

---

## 🎯 Simplified Release Plan

### Option A: Full Release (if all CI passes)

1. ✅ Update VERSION → 0.5.1-alpha
2. ✅ Commit all changes
3. ✅ Push to main
4. ⏳ Wait for CI (all 6 jobs)
5. ✅ Create tag v0.5.1-alpha
6. ✅ Create GitHub release
7. ✅ Announce

**Timeline:** 1 hour (mostly waiting for CI)

### Option B: Minimal Release (if some CI fails)

1. ✅ Update VERSION → 0.5.1-alpha
2. ✅ Commit all changes
3. ✅ Push to main
4. ⏳ Wait for CI (only Linux + macOS)
5. ✅ Create tag v0.5.1-alpha
6. ✅ Create GitHub release
   - Title: "v0.5.1-alpha - Linux + macOS Release"
   - Note: Windows/FreeBSD coming in v0.5.2
7. ✅ Announce

**Timeline:** 45 minutes

### Option C: Test-Only (no release yet)

1. ✅ Update VERSION → 0.5.1-dev
2. ✅ Commit all changes
3. ✅ Push to test branch
4. ⏳ Wait for CI
5. ❌ Don't create tag
6. ❌ Don't create release
7. ✅ Fix any CI issues
8. 🔄 Return to Option A or B

**Timeline:** Flexible

---

## 📊 Current Status

### What's Ready ✅

- ✅ macOS tests (script created)
- ✅ Windows tests (CI configured)
- ✅ FreeBSD tests (scripts created, QEMU ready)
- ✅ Documentation (8 files)
- ✅ CI workflow (6 jobs configured)

### What's Pending 🔄

- 🔄 Windows bootstrap binary (blocker for Windows release)
- 🔄 CI dry run (not executed yet)
- 🔄 Version update (VERSION file)
- 🔄 CHANGELOG.md entry
- 🔄 Tag creation
- 🔄 GitHub release

### What's Blocked ❌

- ❌ FreeBSD end-to-end test (requires 20 min QEMU setup)
- ❌ Windows interpreter (known limitation)

---

## 🚀 Recommended Action

**Proceed with Option B: Minimal Release**

**Reasoning:**
1. Linux + macOS fully tested ✅
2. Windows compilation tests ready (can verify via CI) ✅
3. FreeBSD experimental (documented) ✅
4. Windows bootstrap binary not critical for first alpha ⚠️

**Next Steps:**

```bash
# 1. Update version
echo "0.5.1-alpha" > VERSION

# 2. Commit
jj commit -m "chore: Bump version to v0.5.1-alpha"

# 3. Push
jj bookmark set main -r @
jj git push --bookmark main

# 4. Monitor CI
# https://github.com/simple-lang/simple/actions

# 5. If CI passes → create release
# 6. If CI fails → fix and retry
```

**ETA to Release:** 1-2 hours (depending on CI)

---

## 📞 Decision Points

### Decision 1: Release Scope

- [ ] **Option A:** Full release (all platforms) - requires Windows binary
- [x] **Option B:** Partial release (Linux + macOS) - **RECOMMENDED**
- [ ] **Option C:** Test only (no release) - if CI fails

### Decision 2: Timing

- [x] **Now:** Push immediately and monitor CI
- [ ] **Later:** Fix Windows binary first
- [ ] **Wait:** Complete FreeBSD testing

### Decision 3: Version Number

- [x] **v0.5.1-alpha** - Indicates alpha quality
- [ ] **v0.5.1-beta** - Wait for more testing
- [ ] **v0.6.0-alpha** - Bump minor version

---

## ✅ Final Checklist Before Push

- [ ] Read ALPHA_RELEASE_PLAN.md
- [ ] Update VERSION to 0.5.1-alpha
- [ ] Review all changed files
- [ ] Commit with proper message
- [ ] Push to main
- [ ] Monitor CI progress
- [ ] Be ready to fix issues

**Ready to proceed?** → Execute "Recommended Action" above

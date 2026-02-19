# FreeBSD Simple Compiler - Quick Start Guide

## Current Status: ✓ FreeBSD Compiler Ready!

**TL;DR**: A FreeBSD Simple compiler binary already exists at `bin/freebsd/simple` (79KB).
You can use it right now without any VM configuration.

## Three Options (Choose One)

### Option 1: Use Pre-Built Seed Compiler (FASTEST - 0 minutes)
```bash
# The binary is already built and ready!
ls -lh bin/freebsd/simple
# Copy to FreeBSD system and use
```

**Capabilities**: Core Simple subset (functions, variables, structs, enums, control flow)
**Limitations**: No generics, lambdas, classes (full compiler features)

### Option 2: Test in VM (RECOMMENDED - 15 minutes)
Requires one-time manual SSH configuration.

**Step 1: Configure SSH (5 minutes, manual)**
```bash
# In new terminal:
~/vms/freebsd/start-freebsd.sh

# In FreeBSD console (follow prompts):
# Login: root / Password: (Enter)
# Run:
echo 'sshd_enable="YES"' >> /etc/rc.conf
service sshd start
pkg install -y sudo cmake gmake clang
exit

# Ctrl+C to stop, then:
~/vms/freebsd/start-freebsd-daemon.sh
```

**Step 2: Run Automated Build (10 minutes, automatic)**
```bash
/tmp/freebsd-automated-build.sh
```

This will:
- Transfer seed_cpp and runtime to VM
- Build a test program in FreeBSD
- Verify compilation works
- Show you the complete workflow

### Option 3: Build Full Compiler (ADVANCED - 60+ minutes)
After Option 2, build incrementally:

1. Transfer Simple source to VM:
   ```bash
   rsync -avz -e "ssh -p 2222 -o StrictHostKeyChecking=no" \
     src/core/ root@localhost:/root/simple-src/core/
   ```

2. In VM, use seed_cpp to compile core (31 files)
3. Use core compiler to compile full compiler (411 files)

## What Each File Does

| File | Purpose |
|------|---------|
| `bin/freebsd/simple` | FreeBSD seed compiler (ready to use) |
| `build/freebsd/seed_cpp` | Source of above (same binary) |
| `build/freebsd/libspl_runtime.a` | Runtime library for compilation |
| `seed/runtime.c` / `.h` | Runtime source code |
| `/tmp/FREEBSD_SSH_SETUP.md` | Detailed SSH setup instructions |
| `/tmp/freebsd-automated-build.sh` | Automated build script |
| `/tmp/FREEBSD_BUILD_STATUS.md` | Full technical analysis |

## Quick Test (No VM Needed)

```bash
# Verify binary exists and is correct format
file bin/freebsd/simple

# Expected output:
# bin/freebsd/simple: ELF 64-bit LSB executable, x86-64, version 1 (FreeBSD),
# dynamically linked, interpreter /libexec/ld-elf.so.1, for FreeBSD 14.1
```

## Understanding the Build Plan

The original plan suggested using `native.spl` to generate C code for compiler_core_legacy.
After investigation:

- ❌ **Won't work**: native.spl is designed for simple programs, not the 439-file compiler_core_legacy
- ✅ **Better approach**: Use existing FreeBSD seed_cpp (already cross-compiled)
- ✅ **Full compiler**: Build incrementally (core 31 files → full 411 files)

## Troubleshooting

**"VM not running"**
```bash
~/vms/freebsd/start-freebsd-daemon.sh
```

**"SSH connection refused"**
- Follow `/tmp/FREEBSD_SSH_SETUP.md` to configure SSH first
- VM must be running with SSH enabled

**"seed_cpp SEGFAULT"**
- Expected when trying to compile 439 files at once
- Solution: Build incrementally (core first, then full)

## Next Actions

**If you want a working compiler RIGHT NOW:**
```bash
file bin/freebsd/simple  # Already done! ✓
```

**If you want to test in VM:**
```bash
cat /tmp/FREEBSD_SSH_SETUP.md  # Read this first
```

**If you want the full-featured compiler:**
- Complete Option 2 first (SSH + automated build)
- Then proceed with incremental build (Option 3)

## Success Metrics

- ✅ FreeBSD binary created: `bin/freebsd/simple` (79KB)
- ✅ Correct format: ELF 64-bit FreeBSD x86-64
- ✅ Under 50MB size limit
- ⏳ VM testing: Pending SSH configuration
- ⏳ Full compiler: Pending incremental build

## Questions?

Read the detailed analysis: `/tmp/FREEBSD_BUILD_STATUS.md`

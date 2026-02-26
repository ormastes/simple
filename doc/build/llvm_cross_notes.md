# LLVM cross-build notes (Linux host)

## What we support
- Native Linux build with LLVM backend (`--backend=llvm`).
- Cross to Windows PE/COFF using MinGW sysroot and LLVM/LLD.
- Cross to FreeBSD ELF using downloaded sysroot and LLVM/LLD.
- macOS builds must run on a macOS runner (Mach-O requires Apple SDK/linker).

## Dependencies
- `llvm`, `lld`, `clang`
- Windows: `mingw-w64` (provides headers/libs and gcc driver to call ld.lld)
- FreeBSD: base sysroot (headers+libs) unpacked to `/opt/sysroots/freebsd`

## GitHub Actions workflow
- `.github/workflows/simple-llvm-cross.yml`
  - Ubuntu: build Simple with LLVM; produce Linux binary; emit Windows exe via MinGW + llc.
  - Ubuntu: cross FreeBSD: llc to object, clang/ld.lld with FreeBSD sysroot to exe.
  - macOS: sanity check llc produces Mach-O object (full build should run on mac runner).

## Running locally
```bash
sudo apt-get install llvm lld clang mingw-w64

# Linux object
llc -filetype=obj hello.ll -o hello_linux.o

# Windows object/exe
llc -mtriple=x86_64-w64-windows-gnu -filetype=obj hello.ll -o hello_win.o
x86_64-w64-windows-gnu-gcc hello_win.o -o hello_win.exe -Wl,--strip-all

# FreeBSD object/exe (needs sysroot at /opt/sysroots/freebsd)
llc -mtriple=x86_64-unknown-freebsd13 -filetype=obj hello.ll -o hello_freebsd.o
clang --target=x86_64-unknown-freebsd13 \
  --sysroot=/opt/sysroots/freebsd \
  hello_freebsd.o -o hello_freebsd \
  -fuse-ld=lld -nostdlib \
  /opt/sysroots/freebsd/usr/lib/crt1.o \
  /opt/sysroots/freebsd/usr/lib/crti.o \
  -L/opt/sysroots/freebsd/usr/lib -lc \
  /opt/sysroots/freebsd/usr/lib/crtn.o

# Build Simple with LLVM backend
bin/release/simple build --release --backend=llvm
```

## Notes
- macOS Mach-O cross from Linux isn’t practical due to SDK/licensing; use mac runner.
- `llc`/`ld.lld` are preflight-checked in the workflow to fail fast if missing.

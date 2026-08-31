#!/usr/bin/env bash
cd /c/Users/ormas/dev/simple-rebase
export LLVM_SYS_180_PREFIX="/c/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc"
export INCLUDE="$(grep -E '^INCLUDE=' /tmp/vcenv5.txt | head -1 | cut -d= -f2-)"
export LIB="$(grep -E '^LIB=' /tmp/vcenv5.txt | head -1 | cut -d= -f2-)"
export LIBPATH="$(grep -E '^LIBPATH=' /tmp/vcenv5.txt | head -1 | cut -d= -f2-)"
export PATH="$LLVM_SYS_180_PREFIX/bin:/c/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207/bin/Hostx64/x64:$PATH"
export SIMPLE_WINDOWS_ABI=msvc
export SIMPLE_LINKER_FLAVOR=msvc
# Stale-lock recovery is owned by the lock layer itself
# (scripts/check/lib/portable-process-lock.shs + portable-hardlink-lock.pl):
# claim-state positively detects a dead owner group on MSYS -- including a
# pgid slot recycled by an unrelated Windows process -- and reclaims the
# stale lock; while any genuine group member survives, the lock stays held
# and the surviving member pids are printed on stderr so they can be killed
# deliberately. The old guard here (ps -ef | grep "[b]ootstrap-from-scratch"
# gating rm -rf build/.simple-bootstrap-locks) was broken in BOTH directions
# on MSYS and has been DELETED: MSYS ps never shows script argv (COMMAND is
# only the interpreter path, e.g. /usr/bin/bash), so the grep could never
# match a live bootstrap and the guard deleted a LIVE run's locks -- the
# exact two-bootstraps-one-output binary corruption the lock exists to
# prevent. Never reintroduce an argv-grep here; MSYS ps cannot support one,
# and the launcher must not hand-roll lock logic at all.

# Each run mints a NEW rust-authority-<digest> generation holding a full cargo
# target tree, and nothing garbage-collects the old ones. Five accumulated here
# and took the disk from 25G to 8.5G free, at which point the run died silently
# mid-build (LNK1180 earlier, then no message at all). Keep only generations
# from the current run; the fingerprint-tmp dir is NOT a generation and must be
# excluded from the sweep.
find build/w -maxdepth 1 -type d -name 'rust-authority-*'     ! -name 'rust-authority-fingerprint-tmp' -exec rm -rf {} + 2>/dev/null

exec bash scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap \
  --stop-after-stage2 --output=build/w \
  --progress=build/bootstrap-logs/s2.progress

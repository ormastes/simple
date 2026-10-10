#!/bin/sh
# Diagnostic driver: run the seed-inputs fingerprint with xtrace on failure.
# Branch-only tooling for work/diagnose-seed-fingerprint-20261010.
repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root" || exit 99

mkdir -p diag

{
  echo "PATH=$PATH"
  which rustc cargo cc llvm-config sha256sum perl find awk 2>&1 || true
  rustc -vV 2>&1 || true
  cargo -V 2>&1 || true
  cc --version 2>&1 | head -1 || true
  if command -v llvm-config >/dev/null 2>&1; then
    llvm-config --version 2>&1 || true
    llvm-config --link-static --libfiles 2>&1 || true
    llvm-config --link-static --system-libs 2>&1 || true
  else
    echo "llvm-config: not on PATH"
    ls -d /usr/lib/llvm-*/bin 2>/dev/null || true
  fi
} > diag/env.txt 2>&1

# Replicate bootstrap platform-detect: prepend the detected LLVM bin dir.
if [ -d /usr/lib/llvm-18/bin ]; then
  PATH="/usr/lib/llvm-18/bin:$PATH"
  export PATH
fi
echo "DRIVER_PATH=$PATH" > diag/driver-path.txt

. "${repo_root}/scripts/bootstrap/bootstrap-cache-policy.shs"
BOOTSTRAP_STAGE3_FACADE_PATH="${repo_root}/scripts/check/lib/bootstrap-stage3-provenance.shs"
BOOTSTRAP_STAGE3_VERSION_ROOT=${repo_root}
export BOOTSTRAP_STAGE3_FACADE_PATH BOOTSTRAP_STAGE3_VERSION_ROOT
. "${BOOTSTRAP_STAGE3_FACADE_PATH}"
PORTABLE_LOCK_ATOMIC_HELPER_PATH="${repo_root}/scripts/check/lib/portable-hardlink-lock.pl"
export PORTABLE_LOCK_ATOMIC_HELPER_PATH
. "${repo_root}/scripts/check/lib/portable-process-lock.shs"

export repo_root
sh -x -c '
  . "${repo_root}/scripts/bootstrap/bootstrap-cache-policy.shs"
  BOOTSTRAP_STAGE3_FACADE_PATH="${repo_root}/scripts/check/lib/bootstrap-stage3-provenance.shs"
  BOOTSTRAP_STAGE3_VERSION_ROOT="${repo_root}"
  export BOOTSTRAP_STAGE3_FACADE_PATH BOOTSTRAP_STAGE3_VERSION_ROOT
  . "${BOOTSTRAP_STAGE3_FACADE_PATH}"
  PORTABLE_LOCK_ATOMIC_HELPER_PATH="${repo_root}/scripts/check/lib/portable-hardlink-lock.pl"
  export PORTABLE_LOCK_ATOMIC_HELPER_PATH
  . "${repo_root}/scripts/check/lib/portable-process-lock.shs"
  bootstrap_stage3_seed_inputs_fingerprint "${repo_root}" llvm "--features llvm" "$PATH" x86_64-unknown-linux-gnu
' > diag/inner.out 2> diag/trace.txt
rc=$?
echo "RC=$rc"
tail -80 diag/trace.txt

if [ "$rc" -ne 0 ]; then
  echo "=== phase 2: inspect and attempt apt fix ==="
  ls -la /usr/lib/llvm-18/lib/libPolly.a /usr/lib/llvm-18/lib/libPollyISL.a 2>&1 || true
  dpkg -l | grep -i "llvm-18\|polly" || true
  apt-cache policy libpolly-18-dev 2>/dev/null || true
  sudo apt-get install -y libpolly-18-dev > diag/apt-install.log 2>&1 || true
  tail -5 diag/apt-install.log || true
  ls -la /usr/lib/llvm-18/lib/libPolly.a 2>&1 || true
  sh -x -c '
    . "${repo_root}/scripts/bootstrap/bootstrap-cache-policy.shs"
    BOOTSTRAP_STAGE3_FACADE_PATH="${repo_root}/scripts/check/lib/bootstrap-stage3-provenance.shs"
    BOOTSTRAP_STAGE3_VERSION_ROOT="${repo_root}"
    export BOOTSTRAP_STAGE3_FACADE_PATH BOOTSTRAP_STAGE3_VERSION_ROOT
    . "${BOOTSTRAP_STAGE3_FACADE_PATH}"
    PORTABLE_LOCK_ATOMIC_HELPER_PATH="${repo_root}/scripts/check/lib/portable-hardlink-lock.pl"
    export PORTABLE_LOCK_ATOMIC_HELPER_PATH
    . "${repo_root}/scripts/check/lib/portable-process-lock.shs"
    PATH="/usr/lib/llvm-18/bin:$PATH"
    export PATH
    bootstrap_stage3_seed_inputs_fingerprint "${repo_root}" llvm "--features llvm" "$PATH" x86_64-unknown-linux-gnu
  ' > diag/inner2.out 2> diag/trace2.txt
  rc2=$?
  echo "RC2=$rc2 hash2=$(cat diag/inner2.out)"
  tail -10 diag/trace2.txt
fi
exit 0

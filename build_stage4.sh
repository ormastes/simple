#!/bin/sh
set -e
cd /tmp/claude-1000/-home-ormastes-dev-pub-simple/52b25380-3721-4826-b457-e1371d8b4cb5/scratchpad/wt_fa
PLATFORM=x86_64-unknown-linux-gnu
seed=/tmp/claude-1000/-home-ormastes-dev-pub-simple/52b25380-3721-4826-b457-e1371d8b4cb5/scratchpad/seedfix/target/bootstrap/simple
rtpath=/tmp/claude-1000/-home-ormastes-dev-pub-simple/52b25380-3721-4826-b457-e1371d8b4cb5/scratchpad/seedfix/target/bootstrap
out=build/bootstrap/full/${PLATFORM}/simple
cache=build/bootstrap/native_cache_fixedseed
mkdir -p "build/bootstrap/full/${PLATFORM}" "$cache"
rm -f "$out"
env RUST_LOG=error SIMPLE_BOOTSTRAP=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_BOOTSTRAP_STAGE4=1   SIMPLE_NATIVE_BUILD_TARGET=${PLATFORM} SIMPLE_NATIVE_BUILD_THREADS=4   SIMPLE_NATIVE_BUILD_CACHE_DIR="$cache" SIMPLE_RUNTIME_PATH="$rtpath"   LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_BINARY="$seed"   "$seed" native-build --target ${PLATFORM} --backend cranelift --runtime-bundle core-c-bootstrap   --source src/compiler --source src/app --source src/lib --source examples/10_tooling   --entry-closure --low-memory --threads 4 --cache-dir "$cache" --mode one-binary   --entry src/app/cli/main.spl --runtime-path "$rtpath" -o "$out"
echo "STAGE4_EXIT=$?"; ls -la "$out"

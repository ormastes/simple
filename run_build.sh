#!/bin/bash
set -e
cd /tmp/wt_validate_redeploy
MAIN=/home/ormastes/dev/pub/simple
PLATFORM=x86_64-unknown-linux-gnu
mkdir -p build/validate build/native_cache_validate
env RUST_LOG=error \
  SIMPLE_BOOTSTRAP=1 \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_BOOTSTRAP_STAGE4=1 \
  SIMPLE_NATIVE_BUILD_TARGET="$PLATFORM" \
  SIMPLE_NATIVE_BUILD_THREADS=10 \
  SIMPLE_NATIVE_BUILD_CACHE_DIR="$(pwd)/build/native_cache_validate" \
  SIMPLE_RUNTIME_PATH="$MAIN/src/compiler_rust/target/bootstrap" \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_BINARY="$MAIN/bin/release/$PLATFORM/simple" \
  "$MAIN/bin/release/$PLATFORM/simple" native-build \
  --target "$PLATFORM" \
  --backend llvm \
  --runtime-bundle core-c-bootstrap \
  --source src/compiler --source src/app --source src/lib --source examples/10_tooling \
  --entry-closure \
  --low-memory \
  --threads 10 \
  --cache-dir "$(pwd)/build/native_cache_validate" \
  --mode one-binary \
  --entry src/app/cli/main.spl \
  --runtime-path "$MAIN/src/compiler_rust/target/bootstrap" \
  -o "$(pwd)/build/validate/simple"
echo "BUILD_EXIT=$?"

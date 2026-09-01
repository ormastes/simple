#!/bin/sh
R=/mnt/data/worktrees/wmvk-x86-3
cd $R || exit 9
SEED=$R/src/compiler_rust/target/release/simple
RP=$R/build/simpleos_gpu_host/x86_64-vulkan-cuda-runtime-target/bootstrap
OUT=$R/build/repro/i_owner_bin
LOG=$R/build/repro/i_owner.log
mkdir -p $R/build/repro
SIMPLE_DEBUG_FIELD_ACCESS=1 SIMPLE_BOOTSTRAP_DIAG=1 \
SIMPLE_BINARY="$SEED" SIMPLE_BIN="$SEED" SIMPLE_BOOTSTRAP_DRIVER="$SEED" \
SIMPLE_FRONTEND_DELEGATE="$SEED" SIMPLE_FRONTEND_DELEGATED=1 \
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_LIB="$R/src" \
SIMPLE_LINK_OBJECTS="$RP/libsimple_runtime.a" \
  timeout -k 10s 2400s "$SEED" native-build \
    --backend cranelift --source src/app --source src/lib --entry-closure \
    --entry src/app/repro_iowner/i_owner.spl \
    --runtime-bundle core-c-bootstrap --runtime-path "$RP" \
    --cache-dir $R/build/repro/cache \
    --timeout 2400 --output "$OUT" > $LOG 2>&1
RC=$?
echo "BUILD_RC=$RC" >> $LOG

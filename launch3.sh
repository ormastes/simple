#!/bin/sh
cd /mnt/data/worktrees/stage3clean-1
. scripts/setup/llvm-toolchain-env.shs
export SIMPLE_CACHE_SCOPE=stage3clean1 SIMPLE_TIMEOUT_SECONDS=0
echo "LAUNCH $(date -Is) self=$$"
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 \
  --output=/mnt/data/worktrees/stage3clean-1/build/bootstrap --jobs=4 --progress &
child=$!
echo "CHILD=$child"
wait $child
echo "RC=$? END $(date -Is)"

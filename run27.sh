#!/bin/sh
export SIMPLE_TIMEOUT_SECONDS=0
export SIMPLE_CACHE_SCOPE=run27
export SIMPLE_BOOTSTRAP_EXECUTION_PROFILE=incremental-unlimited
cd /mnt/fast/wt/stage-run27
sh scripts/bootstrap/bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --stop-after-stage2 --jobs=16 --output=/mnt/fast/wt/stage-run27/build/bootstrap
echo "RUN27_SENTINEL_EXIT=$?"

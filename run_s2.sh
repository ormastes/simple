#!/bin/sh
cd /mnt/data/worktrees/lane-boot-s5
export SIMPLE_TIMEOUT_SECONDS=0
sh scripts/bootstrap/bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --stop-after-stage2 --backend=cranelift --jobs=full --output=build/bootstrap/s5 > /mnt/data/worktrees/lane-boot-s5/s2.log 2>&1
RC=$?
echo "STAGE2_RC=$RC" >> /mnt/data/worktrees/lane-boot-s5/s2.log
echo "STAGE2_RC=$RC" > /mnt/data/worktrees/lane-boot-s5/s2.rc

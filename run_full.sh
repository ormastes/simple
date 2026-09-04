#!/bin/sh
cd /mnt/data/worktrees/lane-boot-s5
export SIMPLE_TIMEOUT_SECONDS=0
export SIMPLE_BOOTSTRAP_REASON_RECEIPT=/mnt/data/worktrees/lane-boot-s5/build/bootstrap/admission/a9ab108314e71029da006040f4f82ed0a29cc4e0c2d7dea6ff55b3ce39a6a8e7/planner-admission-v2.env
sh scripts/bootstrap/bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --backend=cranelift --jobs=full --output=build/bootstrap/s5full > /mnt/data/worktrees/lane-boot-s5/full.log 2>&1
RC=$?
echo "FULL_RC=$RC" >> /mnt/data/worktrees/lane-boot-s5/full.log
echo "FULL_RC=$RC" > /mnt/data/worktrees/lane-boot-s5/full.rc

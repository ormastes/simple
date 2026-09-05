# QEMU facade Stage2 closure receipt

- Result: PASS
- Worktree: `/mnt/fast/phase2-facade-closure-fix`
- Compiler: `/mnt/data/worktrees/goal-cache-shadow-freeze/build/bootstrap/versioned-backend/stage2/by-sha/04ce32fa8d913889e33db1670bd11de08bca6d85e375ca21c1970b2ee6deb397/simple`
- Compiler SHA-256: `04ce32fa8d913889e33db1670bd11de08bca6d85e375ca21c1970b2ee6deb397`
- Capsule identity: `2a85ded2acecbf79359e8db486877802e1026785ce0078eafcc258b42fe92a80`
- Exit code: `0`
- Counts: `53 compiled, 0 cached, 0 failed`
- Durable artifact: `/mnt/data/codex-tmp/qemu-facade-final-receipt/qemu_runner.a`
- Artifact SHA-256: `b5b06a223f572868b4e7be8b7342fac785491b66853ef0d19703d8e14eb1a119`
- Complete stdout: `/mnt/data/codex-tmp/qemu-facade-final-receipt/stdout.log` (3 lines, 199 bytes)
- Complete stderr: `/mnt/data/codex-tmp/qemu-facade-final-receipt/stderr.log` (0 lines, 0 bytes)
- Exit-code file: `/mnt/data/codex-tmp/qemu-facade-final-receipt/exit-code.txt`

## Exact environment and argv

```text
SIMPLE_NO_STUB_FALLBACK=1
SIMPLE_NATIVE_BUILD_THREADS=32
SIMPLE_RUNTIME_PATH=/mnt/data/worktrees/goal-cache-shadow-freeze/build/bootstrap/versioned-backend/stage2/by-sha/04ce32fa8d913889e33db1670bd11de08bca6d85e375ca21c1970b2ee6deb397
TMPDIR=/mnt/data/codex-tmp/phase2-facade-qemu-final/tmp
/mnt/data/worktrees/goal-cache-shadow-freeze/build/bootstrap/versioned-backend/stage2/by-sha/04ce32fa8d913889e33db1670bd11de08bca6d85e375ca21c1970b2ee6deb397/simple native-build --source src/compiler --source src/app --source src/lib --source src/os --entry-closure --entry src/os/qemu_runner.spl --backend cranelift --runtime-bundle core-c-bootstrap --emit-archive --timeout 3600 --threads 32 --cache-dir /mnt/data/codex-tmp/phase2-facade-qemu-final/cache --runtime-path /mnt/data/worktrees/goal-cache-shadow-freeze/build/bootstrap/versioned-backend/stage2/by-sha/04ce32fa8d913889e33db1670bd11de08bca6d85e375ca21c1970b2ee6deb397 --output /mnt/fast/phase2-facade-closure-fix/build/test-logs/qemu-facade-final/qemu_runner.a
```

## Complete stdout

```text
Build complete: 53 compiled, 0 cached, 0 failed
  Archive: /mnt/fast/phase2-facade-closure-fix/build/test-logs/qemu-facade-final/qemu_runner.a (2164 KB)
  Time: 3.4s compile + 1.9s link = 5.4s total
```

## Complete stderr

Empty.

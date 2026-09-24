# Build Intermediate Lifecycle Architecture

The CLI owns staging-path creation and stale-start cleanup. The compiler driver owns backend-local scratch cleanup. Both consume the same environment policy, while durable cache ownership remains unchanged.

```text
native-build CLI
  -> scan output parent for old managed staging siblings
  -> configure keep/print policy
  -> driver/backend creates private scratch
  -> publish final artifact atomically
  -> backend removes scratch unless retained
  -> CLI removes failed staging unless retained
```

Only names carrying the exact `.simple-native-build-...tmp` marker and matching the requested output are eligible for start cleanup. Incremental cache directories are outside this classifier.

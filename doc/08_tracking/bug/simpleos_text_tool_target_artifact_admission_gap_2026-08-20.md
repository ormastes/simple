# SimpleOS text tool target artifact admission gap

Status: BLOCKED

The real pure-Simple grep implementation now has a bounded filesystem process
entrypoint and the canonical identity `/usr/bin/grep`. The shell no longer
executes grep through its in-process builtin shortcut.

Execution remains blocked because the image/package pipeline has not produced:

- target-native grep artifact bytes for each admitted SimpleOS triple;
- an independently computed artifact digest;
- a loader-owned authority token binding that digest to `/usr/bin/grep`;
- target evidence covering FAT32, DBFS, and NVFS reads.

Until those artifacts exist, launcher dispatch returns exit 126 with
`TEXT_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE`. Source availability, package
metadata, version output, or help output must not authorize execution.

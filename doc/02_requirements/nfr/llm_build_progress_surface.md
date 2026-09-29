# LLM Build Progress Surface NFRs

- Snapshot size is bounded by eight current files.
- Publication is one atomic file replacement per existing progress emission.
- Steady-state reads are O(snapshot size), independent of event-log length.
- Missing progress is explicit and nonzero from the CLI.
- ETA confidence is explicit; unknown data is never represented as success.


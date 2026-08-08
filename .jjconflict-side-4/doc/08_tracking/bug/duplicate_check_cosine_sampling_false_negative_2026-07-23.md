# Cosine duplicate sampling drops late clones

- **Status:** SOURCE FIXED / STAGE 4 QUALIFICATION PENDING.
- **Observed:** cosine mode discarded every candidate after a round-robin sample
  of 320 blocks, so renamed clones near the end of large files were never
  featureized or compared.
- **Cause:** the legacy sampling cap remained after comparison was replaced by
  the bounded top-five signature-token inverted index.
- **Fix:** remove position-based candidate sampling. Every non-low-signal block
  now reaches the existing index; buckets larger than 400 remain explicitly
  skipped, and each scored pair is deduplicated.
- **Regression:** `detector_grouping_spec.spl` places a renamed clone pair after
  more than 320 earlier candidates and requires both tail blocks in one group.
- **Qualification:** run the focused detector spec and the essential-tools
  duplicate smoke once with the exact admitted Stage 4 CLI.

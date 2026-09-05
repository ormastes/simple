# FAT32 raw LFN validator v1 test plan

- Accept a correctly ordered, checksummed multi-slot LFN and its canonical 8.3 alias.
- Reject missing/duplicate LAST, ordinal gaps, reserved ordinal bits, excess slots, checksum mismatch, nonzero type, and nonzero first cluster.
- Reject premature padding, non-padding after NUL, forbidden/control characters, trailing space/dot, empty or overlength names.
- Accept valid UTF-16 surrogate pairs, including a pair split across slots; reject lone, reversed, or broken pairs.
- Reject noncanonical 8.3 padding and ensure malformed LFN metadata does not expose the following alias.
- Confirm directory lookup and listing use the same acceptance decision.

Runtime execution is deliberately deferred by the parent lane's no-verification instruction.

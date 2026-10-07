# Shared linker regression checks

Run `sh scripts/check/check-link-parity-matrix.shs test/fixtures/linker/parity_sanity/main.spl internal lld mold` with `SIMPLE_BIN` pointing to the qualified self-hosted compiler. Select engines supported by the host and target. The internal route selects Simple's native linker; mold is an explicit external engine. Requested unsupported or unavailable engines fail visibly and the matrix continues to the remaining engines.

Each engine builds the same entry twice, checks deterministic binary identity within that engine, and compares executable output with the interpreter oracle. Different engines need not produce identical binary bytes. Builds default to 40 threads; `SIMPLE_NATIVE_BUILD_THREADS` can override this. Existing native cache configuration remains in effect. Evidence is retained in each reported directory.

A nonzero build exit fails even if an artifact remains. A nonzero interpreter or executable exit also fails, even when its output matches. Output comparison retains the existing trailing-newline normalization. This gate covers executable behavior and determinism; it does not certify all relocations, imports, memory safety, or release readiness.

Use `sh scripts/check/check-link-parity-selftest.shs` to validate six positive/negative harness controls. Its test double deliberately plants failures; a passing selftest is not a real compiler or linker result. Actual engine runs must be reported separately. Use additional regression entries as they become available, preserving their expected failure or behavior oracle rather than declaring success from link exit alone.

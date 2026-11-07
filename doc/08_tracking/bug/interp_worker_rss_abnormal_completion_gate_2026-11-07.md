# RSS gate accepted abnormal completion above its floor

Original reviewed source: PR7500 head95156319e2a68c8c6832ecda2551e994281e0717. The gate saved then discarded the measurement wrapper exit code and judged only peak RSS. A crash or import failure with500000KiB could pass the300000KiB floor and2560000KiB budget.

Repair: preserve and compare wrapper/summary child exits against the actual no-argument worker exit1, require the original internal-entrypoint terminal diagnostic and unique final summary, then judge RSS. Pin SIMPLE_NATIVE_BUILD_WORKER=0 so inherited internal authority cannot alter this observation. Abnormal/missing/inconsistent completion returns ERROR without numeric PASS.

Regression: built-in selftest drives actual gate functions with deterministic above-floor wrapper fixtures for signal139, missing/duplicate terminal, wrong exit, wrapper disagreement and a post-terminal fatal line, plus valid synthetic completion and existing numeric boundary cases.12fixtures passed; shell syntax passed. These are gate tests only, no production RSS/runtime qualification. No sampler implementation or historical measurement record is changed by this repair.

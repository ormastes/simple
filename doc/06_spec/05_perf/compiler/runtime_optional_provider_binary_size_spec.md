# Runtime Optional-Provider Binary Size and Startup Cohorts

BS7 qualifies a minimal NoGC hello and interpreter startup only from an
admitted pure-Simple Stage4 compiler. Development evidence contains at least
30 Simple and 30 Python samples; release evidence contains at least 100 of
each. The checker recomputes p50 and p95 startup and max RSS and requires Simple
to remain within 110% of the same-host Python baseline.

The NoGC binary must be below 2 MiB. Linux release-small additionally requires
at most 15 KiB and at most 105% of the same-toolchain C hello. Other native
formats use an admitted fixed format allowance. Collector sections,
constructors, initialization roots, optional-provider mappings, and provider
initializations must all be absent.

Rust seed and pre-Stage4 measurements are diagnostic only and cannot satisfy
this specification. Heavy native cohorts remain pending until an admitted
Stage4 binary is available.

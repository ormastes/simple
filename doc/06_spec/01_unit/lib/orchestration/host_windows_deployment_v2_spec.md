# Pure Windows deployment provenance records

Source: `test/01_unit/lib/orchestration/host_windows_deployment_v2_spec.spl`.
All six scenarios are **NOT_RUN**. This is an authored source manual; no native
deployment role or passing compiler evidence is inferred from pure records.

1. Derive the fixed physical-machine claim name and matching immutable direct
   child manifest. Require exact authorization-time correlation.
2. Copy the records under another parent or change the manifest root; require
   provenance refusal.
3. Mutate nonce, claim digest, credential digest or enrollment state; refuse
   each mismatch independently.
4. Refuse unknown, oversized and noncanonical records and a manifest time below
   its claim's authorization time. This is record validation, not native-clock
   injection or a claim that runtime regression handling was executed.
5. Supply another parent instead of the installed anchor; reject before native
   acquisition.
6. Exceed the raw byte cap in each of the three caller texts independently;
   reject before allocating transport byte arrays or acquiring a native owner.

Synthetic record data and deterministic test keys are not installed authority.
Actual private parent/claim/child provenance is exercised only by the separate
Windows native companion, which also remains NOT_RUN.

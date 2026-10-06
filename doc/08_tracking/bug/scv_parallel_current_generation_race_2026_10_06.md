# Parallel builds read a moving inventory generation

Windows packet `phase4-cfc-bea-j40` exited 1 after 216.069 seconds with `SCV-E-ADMISSION: source-inventory-digest-mismatch`. Phase3 was acquiring a snapshot concurrently from the same immutable checkout. The log separately reported a workaround-writer lock conflict; that warning is not established as the digest mismatch's root cause.

Source review found two moving-pointer reads after a digest had already been admitted: fresh `compiler_source_authority_validate_v1` and cold HIR validation both read CURRENT. Another invocation publishing generation B between admission and validation can make lane A compare its digest against B despite A's immutable inventory remaining valid. This is a reproducible source-level race consistent with the observed failure; the live log does not capture the exact winning publication.

The candidate reads the admitted digest through `compile_source_inventory_read_at_pointer_v1` at both points. Ownership, generation, snapshot hashes, row membership and corruption rejection stay enabled. Regression scenarios explicitly advance CURRENT between fresh acquisition and validation, and reject wrong generations and unpublished digests. Further snapshot-acquisition races and workaround-writer lock handling remain separate work. Native regression execution is pending; existing active builds are not modified.

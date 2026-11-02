# Windows native checkout violates materializer placeholder contract

Status: OPEN

Actual failed run38169498820 and diagnostic38170943932 prove core.symlinks=true creates a genuine file symlink: tracked blob17 bytes versus dereferenced target2649 bytes. Scope CI selects core.symlinks=false before Windows native checkout; exact production placeholder predicate passes real Git false checkout and rejects true checkout and tampered bytes. Complete Windows native materialization/bootstrap remains pending.

**Revalidated 2026-11-02: still plausible because the report title (Windows native checkout violates materializer placeholder contract) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

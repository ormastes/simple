# Windows native checkout violates materializer placeholder contract

Status: OPEN

Actual failed run38169498820 and diagnostic38170943932 prove core.symlinks=true creates a genuine file symlink: tracked blob17 bytes versus dereferenced target2649 bytes. Scope CI selects core.symlinks=false before Windows native checkout; exact production placeholder predicate passes real Git false checkout and rejects true checkout and tampered bytes. Complete Windows native materialization/bootstrap remains pending.

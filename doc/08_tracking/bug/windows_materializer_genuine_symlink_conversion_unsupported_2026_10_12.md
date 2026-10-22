# Materializer rejects genuine tracked Windows symlinks

Status: OPEN

Diagnostic38170943932 proves a valid genuine link to the exact tracked target is rejected as tampered placeholder bytes. approve-symlink-conversion is parsed/exported but native creation still only accepts a non-reparse placeholder. General conversion remains OPEN; no arbitrary reparse deletion or guard relaxation introduced. Windows CI placeholder configuration is a narrow workaround only.

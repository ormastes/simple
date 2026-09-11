# Environment variant policy handoff application owner V1

The application owner snapshots ambient policy in the parent and appends one
internal argument. It rejects a caller-supplied, missing, duplicate, corrupt,
or oversized internal argument. Worker extraction removes only that argument;
all public flags and their order are preserved.

Project policy is read from `simple.sdn`. User policy is read from the newly
defined, feature-specific `~/.config/simple/config.sdn`; this path is not an
alias for ITF configuration or merged `CompilerConfig` state. Files are read
as bounded regular no-follow inputs.

No authenticated administrator source exists in this slice, so the production
owner supplies empty administrator restrictions. A payload digest must never
be interpreted as administrator authorization.


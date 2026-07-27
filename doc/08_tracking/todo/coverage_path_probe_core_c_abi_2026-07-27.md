# Coverage path-probe core-C ABI

Decision and condition coverage now have a core-C owner. The legacy
`coverage_path` / `coverage_path_end` Simple wrappers still use signatures that
do not match the hosted runtime path ABI, and core-c-bootstrap intentionally has
no path owner. Fix those declarations and add a real path recorder before path
coverage is enabled in compiler instrumentation or release evidence.

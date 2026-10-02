# Native cache linked-directory containment

Executable specification: `test/02_integration/app/test_runner_native_cache_containment_spec.spl`.

Create a private generated native-cache directory, a nested directory link, and a separate task-owned temporary target containing a sentinel. On Windows create an actual junction using the existing process facade; on POSIX create a directory symlink.

Invoke the native artifact cleanup owner against the private cache. Observe that the separate target and its sentinel bytes survive and that the cache link is removed. Remove the separate fixture target only after collecting those observations.

Qualification requires a rebuilt runtime containing the shared no-follow directory-removal provider correction. A source review, lexical prefix guard, or frozen older runtime cannot prove this scenario. Status: spec authored; genuine rebuilt-runtime execution pending.

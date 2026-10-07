# Phase1 directory no-follow extern missing

The seed interpreter failed three bootstrap-owner specs with unknown extern function rt_dir_is_real_no_follow. The native Linux runtime provider exists, but the interpreter dispatch registry omitted the function.

Register a filesystem provider that uses symlink_metadata and accepts only a directory whose final component is not a symlink. On Windows, reject reparse points as well. This preserves the final-component check used by the native provider.

Two registration-level interpreter regressions passed under the enforcing 5859375 KiB watchdog, covering existing directory, regular file, missing path, empty path, directory symlink and dangling symlink. Evidence: /tmp/simple-dir-extern-repair/registration-tests.log and registration-tests.rss.env. The Linux filesystem cases were executed; Windows behavior remains untested here.

Whole seed qualification remains pending. The active sweep continues with its original source and immutable compiler; these repaired cases require verification with a newly built seed.

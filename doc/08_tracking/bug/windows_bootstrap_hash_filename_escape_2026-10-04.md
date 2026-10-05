# Windows bootstrap hash filename escaping

The first source20975 Hello wrapper stopped before compilation because its
Windows backslash path caused GNU sha256sum to prefix the output record with
a backslash. Parsing the first field therefore returned 65 characters rather
than the file's digest. The corrected diagnostic run used stdin hashing and
subsequently compiled and ran Hello successfully.

The reusable phase-verification, provisional-Hello, and managed-phase hash
owners contained the same filename-dependent parsing. They now hash stdin
for providers whose output can escape filenames. Managed phases also retains
the provider's failure status rather than losing it through a cut pipeline.
Existing digest validation remains in force.

The focused regression invokes each production hash definition with a real
SHA256 provider, spaces, and a Windows native backslash path (a literal
backslash filename on Unix), plus missing-file rejection. The provider-failure
test now supplies an existing input and proves the failing provider ran.
These helper checks do not qualify any bootstrap compiler or release.

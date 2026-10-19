# Canonical SMF template file extraction — manual evidence

Requirement REQ-GENERIC-SMF-TYPED-EXTRACTION. Executable owner remains
test/01_unit/compiler/mono/monomorphize/deferred_smf_wrapper_refusal_spec.spl,
reconciling its former unavailable-wrapper oracle. Eight cases UNRUN.

1. Write real canonical SMF containing Code0/TemplateCode1. Check canonical
   memory and file shim lookup find1; load via actual file wrapper in both
   modes and assert body/parameters/binders plus retained earlier definition.
2. Swap whole section entries; find type12 at0. Duplicate type12 and require
   exact ambiguity refusal. No invented section encoder is used.
3. Exercise missing/unknown/duplicate/truncated template sections through real
   files and assert false, error and preserved old rows without new admission.
4. Mutate canonical offset/count fields to overflow/high-bit/truncated bounds,
   including explicit string-table discovery; refuse before indexing/copying.
5. Refuse nonzero/unknown compression, unknown outer major/minor and GTPLv3.
6. Report missing file and short header; recover by reading a real valid file.
7. Accept the canonical writer's empty GTPL transaction without old-row loss;
   exercise supported outer minor0 using a canonical layout control.

Temporary files use secure unique directories, checked writes and cleanup.
No code bytes are executed. No runtime, native ABI, compiler build, memory/perf
measurement or full deferred-body admission PASS is claimed.

8. A real two-record SMF carries a replacement followed by a truncated record. Both modes must retain the earlier cached definition and publish neither staged replacement nor second row.

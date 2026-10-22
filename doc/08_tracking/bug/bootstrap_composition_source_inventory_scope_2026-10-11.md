# Bootstrap composition selectors must remain inside SCV source scope

REQ-BOOTSTRAP-COMPOSITION-SCOPE: native compilation must select checkout-owned
composition sources while retaining the selected CUDA manifest/template identity
and publication evidence. Do not widen SCV admission to arbitrary output roots.

Attempt06 reached the admitted pure-Simple parent's native-build coordinator,
then rejected with `SCV-E-ADMISSION: source-inventory-scope-unsupported` before
compilation. Its transcript selected a CUDA directory under external bootstrap
storage. Parent `0e0287094ba` admits only checkout `src`/`test` inventory
families. The actual generated CUDA file matched the tracked static template,
SHA256 `25ea15e6f7b761fb3bae5263113477eefb580a9f74fb046cdfb10c960d40c73f`.

The shell retains the generated publication directory, manifest/template hashes,
copy verification and source precedence. A separate compiler selector uses
`src` for static CUDA (the real `plugins/...` namespace), or
`src/compositions/cuda_dynamic` / `src/compositions/cuda_disabled`. It selects
the same tracked bytes and checks that the template did not change during
publication. Missing or symlink templates and unsupported modes are rejected.
SCV itself remains responsible for freezing and admitting these source bytes.

The kernel selector is likewise checkout-relative. Its receipt consumer accepts
only its exact canonical absolute or exact checkout-relative spelling, counting
both together; duplicates, wrong owners and traversal spellings cannot satisfy
the existing exactly-one requirement. Content hashes and other K1 policy checks
remain unchanged.

The initial-entry extraction path was also inspected: actual value flags occur
in the parent's consuming table, the entry is relative and inside `src/app`,
and Windows `_fullpath` feeds the existing drive/backslash canonicalizer for
both cwd and entry. No earlier entry-path defect was demonstrated. The error
label is shared by two rejection sites, so its exact executed site was not
claimed proven without an additional diagnostic compiler run.

Validation: the focused shell regression passed using actual production setup,
source argument selection and K1 counting functions. Controlled fixtures copy
the real three CUDA templates, check publication equality, source precedence,
checkout-only roots, tamper refusal and invalid-mode refusal. It also checks
absolute/relative K1 acceptance and duplicate/wrong/traversal rejection. Two
initial test attempts exposed missing sparse-checkout fixture paths; fixture
setup was corrected before the final PASS. No native qualification is implied.
No frozen source, existing receipts or caches were changed during development.

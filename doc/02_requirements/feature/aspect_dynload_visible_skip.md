# Aspect dynload visible partial-success requirement

**Status:** selected by the user request to warn when direct/dynload behavior is
not fully implemented. Automatic packaging remains a separate open requirement.

- **REQ-ASPECT-DYNLOAD-VISIBLE-001:** After a successful launchable
  `native-build --mode dynload`, if the compiler produced zero automatic aspect
  packs, emit exactly one stable named warning on stderr. The warning must state
  that the native artifact remains usable, that dynamic aspect acquisition is
  unavailable, and that `--mode one-binary` is the implemented artifact
  contract.
- Do not warn for `one-binary`, object/archive/shared outputs, failed builds, or
  a future positive automatic-pack receipt.
- Do not advertise an explicit pack-input CLI until such an option exists.

# Bootstrap portability source-owner drift

Status: OPEN. The portability gate retained retired fixture paths, imported-enum and MIR driver owners, bootstrap registry names, and raw runtime names after owner refactoring. This narrow correction uses the reviewed actual owners and equivalent string pointer expressions while preserving registry restoration and fatal error rejection.

Qualification: prior source-contract positive and seven destructive negative fixtures passed. They are persisted as a standalone bounded regression. No compiler, full portability gate, native Mac, baremetal, or FreeBSD execution is claimed. Other second-half findings remain separately recorded: 20 fixture gaps, 27 real gaps, 11 unresolved findings. This patch does not remove their guards.

Production-bound regression: extracts the actual gate predicates and registration/constructor block using diagnostic and owner anchors. Current-source positive, seven destructive source mutations, and a removed production guard rejection passed once. This qualifies the persisted test without executing the full gate.

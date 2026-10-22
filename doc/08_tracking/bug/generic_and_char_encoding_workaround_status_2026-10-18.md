# Generic-instantiation and character-encoding workaround/fix status

Date: 2026-10-18
Scope: release_phase3 Windows stage3 bootstrap. Status tags for two
defect/work streams the release work keeps touching, so the next lane can
tell landed fixes from open workarounds at a glance.

## Character encoding / char wire — STATUS: FIXED (landed)

Symptom class: character-typed enum slots crossing the wire codec carried
nil outside the designated char slots; native char codec draws corrupted
UTF-8/Unicode conversions; HIR-shard char paths faulted.

Landed fixes (verify with `git log --oneline --grep="char\|utf8\|wire"`):
- c5f3f7e34ef fix(compiler): reject wire nil outside character enum slots
- 83764a190dc / native-char-codec-land (#3680): native char codec
- e9964f94c9d test: isolate pure UTF-8 validation for the character wire probe
- e4921124b53 test: probe typed Unicode character wire conversion
- aa51918f1e5 utf8-internal-sosix-plan (#3678): internal UTF-8 transport plan

Workaround note: no consumption-side workaround is carried in-tree for char
encoding as of this writing; the landed fixes are the fix. If a char-wire
fault resurfaces, capture with SIMPLE_HIR_CODEC_ROUNDTRIP=1 (the
HIRROUNDTRIP line names the refusing field) before adding guards.

## Generic instantiation — STATUS: FIXED for bootstrap; HARDENING PLANNED

Landed (bootstrap-blocking fixes):
- 53afb8c62cb (+ parse repairs 2e057996de1, 4893cc0d8a7, hoist a348b74):
  module-global initializers rewritten by mono; `_type_pool_promote_root`
  concretized. Root-caused undefined-symbol link failure
  (doc/08_tracking/bug/generic_instantiation_symbols_never_emitted_test_runner_link_2026-10-16.md).
- This session's optional-transport census (#3574/#3584/#3586, ~103 sites)
  removed the nil/Some-box transports that mis-dispatched generic callees.

PLANNED, not landed (not a bootstrap blocker):
- ad3887b3d54 / 5a4b893357a (#3693): generic formal-verification hardening
  plan — documentation only as of 2026-10-18.

Workaround carried in-tree: none needed for the bootstrap lane; the mono
constants rewrite is the semantic fix and is compiled into every lane since
53afb8c.

## Related open chain (the current stage3 blocker)

The remaining stage3 blocker is the HIR-shard AV frontier (module 2 -> 26 ->
98 -> 141-191 across fix waves; see
stage3_promotion_registry_rewalk_livelock_2026-10-17.md). The newest fix
waves touching the same draw/copy class: #3690 dict-items-native-lowering,
#3691 native-record-copy-absence, 9625bb7a158 registry-membership encoder
probe. Char-encoding and generic fixes above are NOT the blocker; they are
landed.

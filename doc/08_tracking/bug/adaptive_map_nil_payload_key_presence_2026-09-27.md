# Generic adaptive map key presence with nil optional payload (2026-09-27)

Status: OPEN pending interpreter/native execution.

`AdaptiveMap.contains_key` used `self.get(key) != nil`, and `AdaptiveMap.remove` and `OrderedMap.remove` used a nullable value lookup as the existence guard. A key whose value is an optional nil must remain present until removed. Key membership is independent of the stored value.

`AdaptiveMap` now checks keys in its active linear, hash, or ordered storage, while preserving lookup/hit/miss counters for `contains_key`. `AdaptiveMap.remove` and `OrderedMap.remove` use key membership to authorize removal. Focused specs insert an optional nil value, switch the adaptive map through all three algorithms, then remove it; a direct ordered-map case checks the same invariant.

The isolated `build/item7-stage2-stable-site.exe` compiled the focused 28-module native closure with no collection or probe-file failure, but the build failed on unrelated `src/lib/nogc_sync_mut/src/math/rendering.spl`: unresolved `to_latex` on its untyped receiver. See `D:\wk-profile-switchable-item7-20260926\build\item7-optional-map-narrow-build-20260927.log`. No executable was linked, and these new specs have not run on an admitted pure-Simple runner. The behavior remains unverified.

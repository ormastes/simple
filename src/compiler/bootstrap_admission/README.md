These are the canonical bootstrap admission workload entries. They are under
src so native-build can freeze them against its admitted source inventory.
The original scripts/check/cert/redeploy_gate/fixtures copies remain for older
independent checks. The four copies are byte-identical at migration; admission
semantics and expected outputs are unchanged. Bootstrap smoke, receiver-route,
and replay checks use these indexed entries. Producer source snapshots must
capture this placement before compilation; an older image is not retroactively
admitted against a changed source snapshot.

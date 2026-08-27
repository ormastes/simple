#!/bin/sh
# Sequential wave-7 runner over .w7.txt lines 52..561, chunked to keep each
# w7_batch.sh call short; commits every 5 chunks.
cd /tmp/mod14 || exit 1
n=2
start=52
while [ $start -le 561 ]; do
  end=$((start+39)); [ $end -gt 561 ] && end=561
  sh w7_batch.sh $start $end
  start=$((end+1))
  n=$((n+1))
  git add test/ && git -c user.name=guard -c user.email=guard@simple commit -q -m "test(sspec): wave-7 doc recipe — batch $n (lines $((start-40))-$((start-1)))" -- test/ 2>/dev/null || true
done
echo RUNNER_DONE done=$(wc -l < .w7done.txt) skip=$(wc -l < .w7skip.txt) red=$(wc -l < .w7red.txt)

#!/usr/bin/env node

console.log(JSON.stringify({
  reportCount: 132,
  worstByRecall: [
    { sample: "site_119_wordpress", expectedInk: 1490, actualInk: 174, overlapInk: 131, falsePositiveInk: 43, missingInk: 1359, precisionPct10000: 7528, recallPct10000: 879 },
    { sample: "site_15_twitch", recallPct10000: 886 }
  ],
  worstByFalsePositive: [{ sample: "site_31_whatsapp", falsePositiveInk: 64, precisionPct10000: 7730 }]
}, null, 2));

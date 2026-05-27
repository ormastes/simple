#!/usr/bin/env node

console.log(JSON.stringify({
  reportCount: 132,
  worstOverflow: [{ sample: "site_0_google", expectedPixels: 963, actualPixels: 685, missingPixels: 278, actualPct10000: 7113 }],
  worstDivInk: [{ sample: "site_15_twitch", expectedPixels: 1432, actualPixels: 149, actualPct10000: 1040 }],
  worstDiv: [{ sample: "site_60_tripadvisor" }]
}, null, 2));

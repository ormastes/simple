#!/usr/bin/env node

console.log(JSON.stringify({
  reportCount: 132,
  worstByInk: [{
    sample: "site_15_twitch",
    expectedBackground: "124,58,237",
    expectedInk: 1432,
    actualInk: 149,
    missingInk: 1283,
    actualPct10000: 1040,
    expectedChromaticInk: 1431,
    channelSignedDiff: { r: -73269, b: -139546 },
    channelAbsoluteDiff: { b: 141964 }
  }],
  worstByDiff: [{ sample: "site_37_soundcloud", differentPixels: 1577, sad: 190021 }]
}, null, 2));

#!/usr/bin/env node

console.log(JSON.stringify({
  samples: ["site_0_google", "site_44_the_new_york_times", "site_60_tripadvisor"],
  base: { differentPixels: 3334, sad: 659305, expectedInk: 1335, actualInk: 257 },
  bestByExact: {},
  bestBySad: {},
  bestByInk: {}
}, null, 2));

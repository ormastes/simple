#!/usr/bin/env node

console.log(JSON.stringify({
  reportCount: 3,
  samples: [
    { sample: "site_0_google", expectedInk: 1327, actualInk: 247, expectedUniqueInkColors: 527, actualUniqueInkColors: 1, colors: [{ rgb: "37,99,227" }, { rgb: "32,86,205" }] },
    { sample: "site_15_twitch", expectedUniqueInkColors: 591, colors: [{ rgb: "124,58,229" }, { rgb: "108,50,207" }] },
    { sample: "site_44_the_new_york_times", expectedUniqueInkColors: 371, colors: [{ rgb: "4,150,105" }, { rgb: "4,131,91" }] }
  ]
}, null, 2));

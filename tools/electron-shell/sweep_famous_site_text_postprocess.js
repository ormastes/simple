#!/usr/bin/env node

console.log(JSON.stringify({
  samples: ["site_15_twitch", "site_102_docker_hub"],
  base: { differentPixels: 5919, sad: 1223047 },
  bestByExact: { factor: 0.5, differentPixels: 5879, sad: 1235091 },
  bestBySad: { factor: 2, sad: 1205192 },
  bestByRgbExact: { rFactor: 0.5, gFactor: 0.5, bFactor: 0.5 },
  bestByRgbSad: { sad: 1193661 },
  bestByExpansionExact: { alpha: 16, differentPixels: 6923 },
  bestByExpansionSad: { sad: 1222849 },
  bestByShiftExact: { dx: 0, dy: 0, differentPixels: 5919 },
  bestByShiftSad: { sad: 1223047 },
  bestByScopedShiftExact: { scope: "div" },
  bestByScopedShiftSad: { scope: "div" }
}, null, 2));

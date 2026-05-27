#!/usr/bin/env node

const target = process.argv.join(" ");
const isWorst = target.includes("site_44_the_new_york_times");

const base = {
  diffBox: { minX: null, maxY: null },
  channelAbsoluteDiff: { r: 0, g: 0, b: 0 },
  channelSignedDiff: { r: 0, g: 0, b: 0 },
  famousSiteRegions: {
    divBox: { differentPixels: 0 },
    overflowText: { differentPixels: 0 },
    belowOverflow: { differentPixels: 0 }
  },
  textLines: {
    line1: { differentPixels: 0 },
    line3: { differentPixels: 0, sumAbsoluteChannelDiff: 0 }
  },
  textLineSegments: {
    inDiv: { differentPixels: 0 },
    overflow: { differentPixels: 0 }
  },
  expectedNonWhiteBox: {},
  actualNonWhiteBox: {},
  nonWhiteCoverage: [
    { expectedPixels: 1335, actualPixels: 257, missingPixels: 1078, actualPct10000: 1925 },
    { expectedPixels: 963, actualPixels: 685, missingPixels: 278, actualPct10000: 7113 }
  ],
  expectedDominantColor: {},
  actualDominantColor: {},
  expectedInkBox: {},
  actualInkBox: {},
  inkCoverage: {},
  gray: { pixels: 685 },
  chromatic: { pixels: 5444 },
  swatches: [{ pixels: 996 }, { pixels: 776 }, { pixels: 225 }]
};

if (isWorst) {
  base.differentPixels = 3334;
  base.maxY = 95;
  base.sumAbsoluteChannelDiff = 659305;
  base.dark = { pixels: 1031 };
  base.famousSiteRegions.divBox.differentPixels = 1432;
  base.famousSiteRegions.overflowText.differentPixels = 1896;
  base.nonWhiteCoverage.push({ missingPixels: 458, actualPct10000: 7151 });
  base.textLines.line5 = { differentPixels: 0 };
  base.textLineSegments.inDiv = { differentPixels: 707, sumAbsoluteChannelDiff: 193625, pixels: 302 };
  base.textLineSegments.overflow = { pixels: 226 };
} else {
  base.differentPixels = 0;
  base.sumAbsoluteChannelDiff = 0;
}

console.log(JSON.stringify(base, null, 2));

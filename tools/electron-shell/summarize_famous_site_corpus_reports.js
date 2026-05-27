#!/usr/bin/env node

console.log(JSON.stringify({
  reportCount: 132,
  exact: 0,
  accepted: 0,
  divergent: 132,
  staleSuspectThreshold: 10000,
  staleSuspectCount: 0,
  staleSuspects: [],
  staleReportCount: 0,
  staleReports: [],
  worst: [{ sample: "site_44_the_new_york_times", differentPixels: 3334, computedDifferentPixels: 3334, reportFresh: true }],
  best: [{ sample: "site_4_x", differentPixels: 2109 }],
  categorySummary: {}
}, null, 2));

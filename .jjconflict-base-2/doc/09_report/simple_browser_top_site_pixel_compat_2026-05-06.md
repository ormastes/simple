# Simple Browser Top-Site Pixel Compatibility Audit

Date: 2026-05-06

Ranking basis: Semrush “Most Visited Websites in the World, Updated March 2026” (last updated 2026-04-13). Local renderer basis: checked-in `test/fixtures/famous_site_corpus/manifest.sdn` and matching Chrome/Simple PPM comparison reports under `test/baselines/famous_site_corpus/`.

## Summary

- Local corpus samples checked: 132
- Semrush top-20 entries covered by local corpus: 14/20
- Covered Semrush top-20 accepted: 14/14
- Covered Semrush top-20 exact: 14/14
- Full local corpus exact/accepted: 132/132 exact, 132/132 accepted
- Worst local different_pixels: 0
- Worst local max_channel_diff: 0

## Semrush Top 20 Coverage

| Rank | Domain | Site | Covered | Corpus ID | Diff px | Match/10000 | Perceptual/10000 | Max channel diff | Accepted |
|---:|---|---|---|---|---:|---:|---:|---:|---|
| 1 | google.com | Google | Yes | site_0_google | 0 | 10000 | 10000 | 0 | true |
| 2 | youtube.com | YouTube | Yes | site_1_youtube | 0 | 10000 | 10000 | 0 | true |
| 3 | facebook.com | Facebook | Yes | site_2_facebook | 0 | 10000 | 10000 | 0 | true |
| 4 | instagram.com | Instagram | Yes | site_3_instagram | 0 | 10000 | 10000 | 0 | true |
| 5 | chatgpt.com | ChatGPT | Yes | site_20_chatgpt | 0 | 10000 | 10000 | 0 | true |
| 6 | reddit.com | Reddit | Yes | site_8_reddit | 0 | 10000 | 10000 | 0 | true |
| 7 | wikipedia.org | Wikipedia | Yes | site_6_wikipedia | 0 | 10000 | 10000 | 0 | true |
| 8 | x.com | X | Yes | site_4_x | 0 | 10000 | 10000 | 0 | true |
| 9 | pornhub.com | Pornhub | No |  |  |  |  |  |  |
| 10 | whatsapp.com | WhatsApp | Yes | site_31_whatsapp | 0 | 10000 | 10000 | 0 | true |
| 11 | xvideos.com | XVideos | No |  |  |  |  |  |  |
| 12 | yahoo.com | Yahoo | Yes | site_13_yahoo | 0 | 10000 | 10000 | 0 | true |
| 13 | amazon.com | Amazon | Yes | site_7_amazon | 0 | 10000 | 10000 | 0 | true |
| 14 | tiktok.com | TikTok | Yes | site_5_tiktok | 0 | 10000 | 10000 | 0 | true |
| 15 | duckduckgo.com | DuckDuckGo | No |  |  |  |  |  |  |
| 16 | bing.com | Bing | Yes | site_14_bing | 0 | 10000 | 10000 | 0 | true |
| 17 | yahoo.co.jp | Yahoo Japan | No |  |  |  |  |  |  |
| 18 | linkedin.com | LinkedIn | Yes | site_10_linkedin | 0 | 10000 | 10000 | 0 | true |
| 19 | xhamster.com | XHamster | No |  |  |  |  |  |  |
| 20 | microsoftonline.com | Microsoft Online | No |  |  |  |  |  |  |

## Top 10 Different Local Corpus Pages

All checked-in local corpus pages are exact matches, so the top-10 “different” list is a zero-difference tie.

| # | Site | Corpus ID | Diff px | Match/10000 | Perceptual/10000 | Max channel diff | Accepted |
|---:|---|---|---:|---:|---:|---:|---|
| 1 | Google | site_0_google | 0 | 10000 | 10000 | 0 | true |
| 2 | YouTube | site_1_youtube | 0 | 10000 | 10000 | 0 | true |
| 3 | LinkedIn | site_10_linkedin | 0 | 10000 | 10000 | 0 | true |
| 4 | MDN | site_100_mdn | 0 | 10000 | 10000 | 0 | true |
| 5 | npm | site_101_npm | 0 | 10000 | 10000 | 0 | true |
| 6 | Docker Hub | site_102_docker_hub | 0 | 10000 | 10000 | 0 | true |
| 7 | Hugging Face | site_103_hugging_face | 0 | 10000 | 10000 | 0 | true |
| 8 | Kaggle | site_104_kaggle | 0 | 10000 | 10000 | 0 | true |
| 9 | arXiv | site_105_arxiv | 0 | 10000 | 10000 | 0 | true |
| 10 | PubMed | site_106_pubmed | 0 | 10000 | 10000 | 0 | true |

## First 20 Local Famous-Site Corpus Pages

| # | Site | Corpus ID | Diff px | Match/10000 | Perceptual/10000 | Max channel diff | Accepted |
|---:|---|---|---:|---:|---:|---:|---|
| 1 | Google | site_0_google | 0 | 10000 | 10000 | 0 | true |
| 2 | YouTube | site_1_youtube | 0 | 10000 | 10000 | 0 | true |
| 3 | Facebook | site_2_facebook | 0 | 10000 | 10000 | 0 | true |
| 4 | Instagram | site_3_instagram | 0 | 10000 | 10000 | 0 | true |
| 5 | X | site_4_x | 0 | 10000 | 10000 | 0 | true |
| 6 | TikTok | site_5_tiktok | 0 | 10000 | 10000 | 0 | true |
| 7 | Wikipedia | site_6_wikipedia | 0 | 10000 | 10000 | 0 | true |
| 8 | Amazon | site_7_amazon | 0 | 10000 | 10000 | 0 | true |
| 9 | Reddit | site_8_reddit | 0 | 10000 | 10000 | 0 | true |
| 10 | Netflix | site_9_netflix | 0 | 10000 | 10000 | 0 | true |
| 11 | LinkedIn | site_10_linkedin | 0 | 10000 | 10000 | 0 | true |
| 12 | Microsoft | site_11_microsoft | 0 | 10000 | 10000 | 0 | true |
| 13 | Apple | site_12_apple | 0 | 10000 | 10000 | 0 | true |
| 14 | Yahoo | site_13_yahoo | 0 | 10000 | 10000 | 0 | true |
| 15 | Bing | site_14_bing | 0 | 10000 | 10000 | 0 | true |
| 16 | Twitch | site_15_twitch | 0 | 10000 | 10000 | 0 | true |
| 17 | Discord | site_16_discord | 0 | 10000 | 10000 | 0 | true |
| 18 | GitHub | site_17_github | 0 | 10000 | 10000 | 0 | true |
| 19 | Stack Overflow | site_18_stack_overflow | 0 | 10000 | 10000 | 0 | true |
| 20 | OpenAI | site_19_openai | 0 | 10000 | 10000 | 0 | true |

## Validation Commands

- `node tools/electron-shell/verify_famous_site_corpus_completion.js --expected-count=132`
- `bin/simple test test/sys/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --no-cache`
- `bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl --mode=interpreter --no-cache`

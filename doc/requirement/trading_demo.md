# Trading Agent Comparison Demo — Requirement

## Feature Name
`trading_demo` — Gather historical stock data and run demo backtests with different agent strategies to compare profit in normal vs crisis market conditions.

## Motivation
The trading system has 5 seed strategies but no way to demonstrate them end-to-end. Users need to see how different strategies perform across market regimes (normal, crisis) without requiring LLM API keys.

## Scope

### In Scope
- Demo script that fetches real OHLCV data from KRX for Samsung (005930)
- Rule-based strategy engines that approximate each LLM strategy's behavior (no API keys needed)
- Backtest each strategy on a normal market period and a crisis market period
- Print comparison report showing profit/loss, drawdown, win rate per strategy per regime
- Identify which strategy performs best overall and per regime

### Out of Scope
- Real LLM API calls (demo should work offline after data fetch)
- Multi-ticker portfolios
- Training/genetic algorithm (that's a separate workflow)

## Acceptance Criteria
1. Data fetch: OHLCV files created for at least one ticker covering normal + crisis periods
2. Rule-based engines: 5 strategies produce BUY/SELL/HOLD decisions based on price patterns
3. Backtest runs: Each strategy evaluated on both normal and crisis date ranges
4. Report: Clear comparison table showing all strategies × all regimes with key metrics
5. Regime detection: Automatically classifies fetched periods

## Dependencies
- `trading/main.spl` — existing CLI and backtest infrastructure
- `trading/feature/data_pipeline/` — fetcher, storage
- `trading/feature/backtester/` — executor, cost_model
- `trading/feature/evaluator/` — metrics_calc
- `trading/feature/data_pipeline/regime_detector.spl`

## I/O Examples

### Input
```
bin/simple run examples/korean_stock_mcp/trading/demo.spl
```

### Output
```
=== Stock Trading Agent Demo ===

Fetching OHLCV data for 005930 (Samsung Electronics)...
  Normal period: 20240101 ~ 20240630 (120 bars)
  Crisis period: 20200101 ~ 20200630 (118 bars)

=== Normal Market Results (2024-01 ~ 2024-06) ===
Strategy             | Return  | MaxDD   | WinRate | Trades
---------------------|---------|---------|---------|-------
Fundamental Value    |  +3.2%  |  -4.1%  |   62%   |   8
Momentum Trader      |  +5.8%  |  -6.2%  |   55%   |  22
Mean Reversion       |  +2.1%  |  -3.5%  |   58%   |  15
Sentiment Analyst    |  +1.4%  |  -5.0%  |   50%   |  12
Balanced Portfolio   |  +2.8%  |  -2.9%  |   65%   |   6

=== Crisis Market Results (2020-01 ~ 2020-06) ===
Strategy             | Return  | MaxDD   | WinRate | Trades
---------------------|---------|---------|---------|-------
Fundamental Value    |  -8.2%  | -22.1%  |   40%   |  10
Momentum Trader      | -12.5%  | -28.3%  |   35%   |  30
...

=== Best Performers ===
Normal: Momentum Trader (+5.8%)
Crisis: Balanced Portfolio (-1.2%)
Overall: Fundamental Value (+1.5% avg)
```

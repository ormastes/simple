# RV32 NVMe NAND Read-Level Detail Design

## RAM words

| Word | Meaning |
|---:|---|
| 0 | magic/version |
| 1 | lifecycle stage |
| 2 | page state: erased/programmed |
| 3 | programmed data word |
| 4 | stored threshold level |
| 5 | selected read reference |
| 6 | read count |
| 7 | refresh count |
| 8 | recovery count |
| 9 | last operation status |
| 10..11 | admin queue id/depth |
| 12..13 | user/I/O queue id/depth |
| 14..15 | admin/I/O queue lifecycle state |
| 16..20 | SQ tail/head, CQ tail/head, completion count |
| 21..22 | block read count and neighbor threshold level |
| 23..25 | retirement count, remap count, verify-failure injection |
| 26..30 | retry direction/index, ECC error count/budget, FCR phase |
| 31..34 | run count, cell polarity, neighbor data/polarity |
| 35..36 | successful downward/upward retry indices |
| 37..38 | active-page and neighbor SECDED words |
| 39..44 | alternate-slot state/data/level/ECC/polarity and active slot |
| 45..46 | last independently decoded data and queue rejection count |

The linker reserves 256 bytes, leaving headroom without adding dynamic layout.
The initial erased level is 32; program level is 160; default reference is 128.
Retention uses `128,120,112,104`; disturb uses `128,136,144,152`. Threshold
distance produces zero to four raw bit errors. With an ECC budget of one,
retention level 116 and disturb level 140 reject the default read and become
correctable at retry index one. Retry selection never reads the hidden level.

Lifecycle stages are reset, ready, admin-ready, and I/O-ready. Commands before
their prerequisite stage return a state error. Program on a programmed page
returns a media error. SQ/CQ indices advance only for a live I/O queue and reject
full/empty operations. The prevention threshold is four block reads; neighboring
cell drift is checked and refreshed. FCR requires ECC correction plus an exact
payload match, then erase/program/read-verify. Verification failure increments
retirement and remap counters and remains a media error.

UART markers are stable API: `NAND STARTUP PASS`, `NAND ADMINQ PASS`,
`NAND IOQ PASS`, `NAND ERASE PASS`, `NAND PROGRAM PASS`, `NAND READ PASS`,
`NAND PREVENT PASS`, `NAND EVIDENCE D1 U1 F5 C3 T1 M1 Q3 X2 S1 PASS`, and
`NAND RECOVERY PASS`. The AXI rehearsal requires nonzero `.nandram` reads and
writes while recovering the complete transcript over AXI4-Lite. Physical BRAM
evidence is captured by the UART and read unchanged through JTAG USER4.

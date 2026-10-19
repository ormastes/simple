# Brotli official test vectors

Source: github.com/google/brotli, tests/testdata (MIT license). Each pair is <name> (plaintext) and <name>.compressed (brotli stream). These are the absolute oracle for the decoder; never edit them. Git blob sha per file (verified with git hash-object):

- 10x10y  3f9cf8651c95f006109c6d04e15fe3e26e477fe1
- 10x10y.compressed  3769516d943745d67d3873caf4e9149e95d4b73d
- 64x  caa41718cb20530713fa29098bed86e019eebd32
- 64x.compressed  74d0be10a7ded87c29f81b65a8637ce52e2d0c88
- cp852-utf8  fa14705c156df0227e5847800c93cb233063741e
- cp852-utf8.compressed  12ba6c24700de7615d34766d27442aab11b068c8
- empty  e69de29bb2d1d6434b8b29ae775ad8c2e48c5391
- empty.compressed  f8fa5a235408d5c6f2c2844e44cd98c1fa666ac8
- monkey  47408cd685dc7256fa95f1abdb47a072138a041d
- monkey.compressed  bbcf134402c5e5b921d339850cdc2e1d815e88a7
- quickfox  ff3bb63948b4b24796d2acd259915f2a9d972638
- quickfox.compressed  b5deebc42f4277d50d4d02f127819cf298e1f662
- ukkonooa  1072b69b4fa079b36330958f87f0bc15c343db65
- ukkonooa.compressed  f39f068d7ea93d939faff47954cbb3d6049f63bb
- x  500c0709ca24338426091ca19777e13a1920ebdf
- x.compressed  2a44b5def2201712a8261bdb95a5528341e0570b
- xyzzy  fbfb23d1efdb5ce7f2f24518ee1bd718a037a17d
- xyzzy.compressed  e6982cef480da0d7674729f4de32f76968c7402b

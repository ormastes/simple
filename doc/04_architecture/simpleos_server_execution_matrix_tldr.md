# SimpleOS server execution matrix — TLDR

Three real modes share one bounded receipt: ARM64 QEMU CPU, UNO Q CPU, and UNO
Q GPU. Mutable server/DB/filesystem state has one parent owner. Optional GPU
workers receive immutable input and return validated results. Linux comparison
uses equivalent public protocols; CUDA never stands in for networking or
durability. Marker, host, x86, and Linux-as-SimpleOS substitutions fail closed.

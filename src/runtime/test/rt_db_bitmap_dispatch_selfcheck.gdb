set pagination off
set confirm off
set $avx512_hits = 0
break db_bitmap_and_avx512
commands
silent
set $avx512_hits = $avx512_hits + 1
continue
end
run
printf "AVX512_KERNEL_ENTRIES=%d\n", $avx512_hits
if $_exitcode != 0
quit 2
end
if $avx512_hits != 3
quit 3
end
quit 0
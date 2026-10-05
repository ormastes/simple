set pagination off
set confirm off
set $avx2_hits = 0
break db_bitmap_and_avx2
commands
silent
set $avx2_hits = $avx2_hits + 1
continue
end
run
printf "AVX2_KERNEL_ENTRIES=%d\n", $avx2_hits
if $_exitcode != 0
quit 2
end
if $avx2_hits != 3
quit 3
end
quit 0
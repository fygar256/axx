X=../x86_64.axx
caxx $X a64rt_axx_freebsd.s --osabi FreeBSD -o a64rt.o      # ランタイム（1回だけ）
caxx a64tox64_axx.axx bf_aarch64.s -V | cat a64ext.s - > bf_x64.s
caxx $X bf_x64.s --osabi FreeBSD -o bf.o
ld -static -e __a64_start bf.o a64rt.o -o bf
./bf mandelbrot.bf | head -4 

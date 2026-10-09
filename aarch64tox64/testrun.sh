X=../x86_64.axx
caxx $X a64rt_axx.s -o a64rt.o      # ランタイム（1回だけ）
caxx a64tox64_axx.axx bf_aarch64.s -V | cat a64ext.s - > bf_x64.s
caxx $X bf_x64.s -o bf.o
ld -static -e _start bf.o a64rt.o -o bf
brandelf -t Linux bf
brandelf -l bf
./bf mandelbrot.bf

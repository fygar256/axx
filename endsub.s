; ===================================================================
;  endsub.s -- endsub.axx の試験ソース
;
;    axx.py endsub.axx endsub.s -b endsub.bin
;    caxx   endsub.axx endsub.s -b endsub.bin
; ===================================================================

        movr1   a,0x22
        movr2   a,0x33
        movr3   a,0x44

        addx
        addy

        lda1
        ldb2

        cntd5
        cntd7

; datadir_err.s -- .db / .dw / .dd / .dq / .do などの誤り（Technical_Manual 5.3）
;
; どの行もエラーになる。誤った値の分も 0 のワードを出すので、後ろの行の
; 番地はずれない。
;
;   axx datadir.axx datadir_err.s -b out.bin
        .db     256
        .db     -129
        .dw     0x10000
        .dd     0x100000000
        .do     0x100000000000000000000000000000000
        .do     "x"
        .db
        .dw     1,
        .dw     "ab"
        .db     "abc" junk
        .dd     no_such_label
        .db     1 2
        .db     "\x"
        .dq     0xffffffffffffffff, -0x8000000000000000   ; これは通る

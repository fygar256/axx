; datadir.s -- ソース側の .db / .dw / .dd / .dq / .do / .dy / .dz（Technical_Manual 5.3）
;
;   axx datadir.axx   datadir.s -v       8 ビット、下位のワードから
;   axx datadirbe.axx datadir.s -v       8 ビット、上位のワードから
;   axx datadirw.axx  datadir.s -v       16 ビットワード
;   axx datadir.axx   datadir.s -o out.o ELF（ラベルにはリロケーションが付く）
        .extern ext
        .section .text
start:  nop
        .db     1, 2, -1, 0xff, 'A', ','        ; 数と文字定数
        .DB     "Hi\n", 0, "\x41あ"         ; 文字列（.ascii と同じ規則）
        .dw     0x1234, -2, (1+2)*3
        .dd     0x12345678, -0x80000000, 0xffffffff
        .dq     0x1122334455667788, -1
        .do     0x112233445566778899aabbccddeeff00, -1
        .dy     1                               ; 式の値は 256 ビットの符号付き
        .DZ     -2                              ; 256 ビットより上は符号拡張
        .dw     end-start                       ; 同じセクションのラベル差
end:    nop
        .endsection
        .section .data
tbl:    .dq     start, end+4                    ; ラベル
        .dd     ext, ext+8                      ; 外部のシンボル
        .dd     fwd                             ; 前方参照
        .dw     fwd-tbl
fwd:    .db     "end", 0
        .endsection

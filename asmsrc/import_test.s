; import_test.s -- -i のインポートファイルの読み方の回帰テスト（z80.axx、import_test.tsv）
; 値は 16 進。符号・0x・前後の空白は任意。-e / -E が書く -0x5 や 64 ビット超えも読める
 LD BC,neg
 LD BC,neg2
 LD BC,lab
 LD BC,dat
 LD BC,sp1
 LD A,big&0xff
 LD A,(big>>64)&0xff
 LD BC,upper
 JP lab

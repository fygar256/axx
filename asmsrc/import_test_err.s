; import_test_err.s -- import_test_err.tsv の読めない値（16 進以外の数字・下線・
; 符号の重なり・2**192 以上）は行ごと捨てられ、ラベルは未定義になる
 LD BC,u1
 LD BC,u2
 LD BC,u3
 LD BC,u4
 LD BC,u5
 LD BC,ok

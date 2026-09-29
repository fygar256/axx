; Demonstration source for aarch64_logical_mini.axx
; Assemble with:  ./caxx aarch64_logical_mini.axx aarch64_logical_demo.s -v -b out.bin

AND  X0,X1,#0xf
ORR  X2,X3,#0xff00
EOR  X4,X5,#0x5555555555555555
ANDS X6,X7,#0x0f0f0f0f0f0f0f0f
AND  SP,X8,#0x3
ANDS XZR,X9,#0xff
TST  X10,#0x8000000000000001

AND  W0,W1,#0xf
ORR  W2,W3,#0xff00ff00
EOR  W4,W5,#0x55555555
ANDS W6,W7,#0x0f0f0f0f
AND  WSP,W8,#0x3
ANDS WZR,W9,#0xff
TST  W10,#0x80000001

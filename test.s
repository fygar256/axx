ldf a,flt{3.14}
ldd a,dbl{3.14}
ldq a,qad{3.14}
leaq rax , [ rbx , rcx , 2 , 0x40]
leaq rax , ( rbx + rcx * (2+2) + 0x40 )
addi $v0,$a0,5
vmov.f32 s0,#3.14
st1 {v0.4s},[x0]
add r1, r2, r3 lsl #20
rep movsb
per movsb
movsb
load a,[b]
repeat 10
ldf a,label
label: .equ flt{3.14}
ldf a,flt{enfloat(:label)*2}

; .call の文字列の戻り値をテキストとして出す
start:	mov	a,b		; ラベルとコメント付き
	mov	h,l
    jmp	loop
loop:	mvi	c,msg+1	; テンプレートと並べる
	semi	foo
	semi0
	drop	; 捨てる
here:	empty	; 空文字列
	chr
	emitret
	num
	xyzzy	; マッチしない行

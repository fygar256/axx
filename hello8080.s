        .org 0x100       ; .COM は 0x100 にロードされる
start:
        mvi c,9          ; BDOS function 9 = print $-terminated string
        lxi d,msg        ; DE = アドレス of msg
        call 0x0005      ; BDOS entry at 0005h
        ret              ; CP/M に戻る

msg:    db 'Hello, world$'

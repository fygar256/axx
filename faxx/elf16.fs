\ elf16.fs -- ELF オブジェクトの書き出し (7): ヘッダとファイル

decimal

variable h-flags  variable h-ver  variable h-entry  variable h-osabi  variable h-abiv
variable ehdr-size

: hdr@ ( a u def -- v ) { a u def } a u d-hdr om-find ?dup if @ else def then ;

: pack-ehdr ( etype emach shoff shnum shstrndx sb -- ) { et em shoff shnum shstrndx sb }
  s" type" et hdr@ 65535 and to et
  127 sb put8  69 sb put8  76 sb put8  70 sb put8
  w-64 @ if 2 else 1 then sb put8
  w-le @ if 1 else 2 then sb put8
  1 sb put8  h-osabi @ sb put8  h-abiv @ sb put8  7 sb put-zero
  et sb put16  em sb put16  h-ver @ sb put32
  w-64 @ if
    h-entry @ sb put64  0 sb put64  shoff sb put64
    h-flags @ sb put32  ehdr-size @ sb put16  0 sb put16  0 sb put16  64 sb put16
    shnum sb put16  shstrndx sb put16
  else
    h-entry @ sb put32  0 sb put32  shoff sb put32
    h-flags @ sb put32  ehdr-size @ sb put16  0 sb put16  0 sb put16  40 sb put16
    shnum sb put16  shstrndx sb put16
  then ;

: pack-shdr ( name type flags addr off size link info align entsize sb -- ) { nm ty fl ad off sz lk inf al es sb }
  nm sb put32  ty sb put32
  w-64 @ if
    fl sb put64  ad sb put64  off sb put64  sz sb put64  lk sb put32  inf sb put32  al sb put64  es sb put64
  else
    fl sb put32  ad sb put32  off sb put32  sz sb put32  lk sb put32  inf sb put32  al sb put32  es sb put32
  then ;

: pad-to ( off sb -- ) { off sb } begin sb bb-len off < while 0 sb sb-c repeat ;

: default-align ( type -- n ) 7 = if 4 else 16 then ;
: cs-align ( i -- n ) { i } i cells cs-al + @ dup 0< if drop i cells cs-ty + @ default-align then ;

\ ---- 準備 ----
variable wr-native  variable wr-eff
: wr-prelude ( -- )
  endian-big @ 0= if 1 else 0 then w-le !
  mach-table
  mt-class@ wr-native !
  elf-class-cli @ ?dup if else wr-native @ then wr-eff !
  wr-eff @ wr-native @ <> if
    mb-reset s"  warning - -f forced ELF" mb+ wr-eff @ 2 = if s" 64" else s" 32" then mb+
    s"  for machine " mb+ elf-machine @ mb-n s" , whose conventional class is ELF" mb+ wr-native @ 2 = if s" 64" else s" 32" then mb+
    s" ; writing a non-default (but well-formed) combination." mb+ mb-get diag-w
  then
  wr-eff @ 2 = if 1 else 0 then w-64 !
  w-64 @ if 64 else 52 then ehdr-size !
  s" flags" 0 hdr@ 4294967295 and h-flags !
  s" version" 1 hdr@ 4294967295 and h-ver !
  s" entry" 0 hdr@ word-mask-v h-entry !
  s" osabi" elf-osabi-v @ hdr@ 255 and h-osabi !
  s" abiversion" 0 hdr@ 255 and h-abiv ! ;

\ ---- 構成 ----
variable nrela
create rso MAXSEC cells allot                      \ リロケーションのあるセクション (1 始まり)
create rdata MAXSEC cells allot                    \ その中身 (sb)
create rname-off MAXSEC cells allot  create roff MAXSEC cells allot
create soff MAXSEC cells allot                     \ セクションのファイル内の位置
create gname-off MAXGRP cells allot  create goff MAXGRP cells allot  create gdata MAXGRP cells allot  create ginfo MAXGRP cells allot
create dpname-off 4 cells allot  create dpoff 4 cells allot  create dpsb 4 cells allot
create drname-off 2 cells allot  create droff 2 cells allot  create drsb 2 cells allot  create drkind 2 cells allot
variable ndbgp  variable ndbgr
variable shs  variable sh-symtab-name  variable sh-strtab-name  variable sh-shstr-name
variable sh-eh-name  variable sh-ehr-name  variable sh-xidx-name
variable need-xidx  variable has-eh
variable eh-data-sb  variable eh-rdata-sb  variable xidx-sb

: rela-prefix ( -- a u ) mt-rela? if s" .rela" else s" .rel" then ;

: wr-rela-order ( -- )
  0 nrela !
  ncs @ 0 ?do
    i 1+ sec-has-relocs? if i 1+ nrela @ cells rso + !  1 nrela +! then
  loop ;

: dw-pack-relas ( at-arr si-arr rt-arr ad-arr n -- sb ) { aa sa ra da n }
  bb-new { b }
  n 0 ?do
    mt-rela? if aa i cells + @ sa i cells + @ ra i cells + @ da i cells + @ qn b pack-rela
    else aa i cells + @ sa i cells + @ ra i cells + @ b pack-rel then
  loop
  b ;

: wr-dwarf ( -- )
  0 ndbgp !  0 ndbgr !
  gen-debug @ 0= lm-n @ 0= or if exit then
  dw-check 0= if exit then
  dwr-init
  dw-collect-labels
  0 lm@ dup @ swap cell+ @ cs-find 1+ dup 0= if drop 1 then dw-prim-idx !
  dw-prim-idx @ 1- cells cs-sz + @ dw-prim-size !
  dw-nlab @ 0> dw-abbrev
  dw-build-info
  dw-build-line
  3 ndbgp !
  dw-sb-abbrev @ 0 cells dpsb + !  dw-sb-info @ 1 cells dpsb + !  dw-sb-line @ 2 cells dpsb + !
  0 ndbgr !
  dwi-n @ if
    dwi-at @ dwi-si @ dwi-rt @ dwi-ad @ dwi-n @ dw-pack-relas ndbgr @ cells drsb + !
    0 ndbgr @ cells drkind + !  1 ndbgr +!
  then
  dwl-n @ if
    dwl-at @ dwl-si @ dwl-rt @ dwl-ad @ dwl-n @ dw-pack-relas ndbgr @ cells drsb + !
    1 ndbgr @ cells drkind + !  1 ndbgr +!
  then ;


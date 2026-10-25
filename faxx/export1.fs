\ export1.fs -- -e / -E の書き出し (axx.py の _write_export)

decimal

sb-new constant ex-sb
: ex-hexq ( q -- ) false q>hex { a u }                  \ Python の {x:#x}
  a c@ 45 = if s" -0x" ex-sb sb+ a 1+ u 1- ex-sb sb+ else s" 0x" ex-sb sb+ a u ex-sb sb+ then ;
: ex-hex ( n -- ) qn ex-hexq ;
: ex-tab ( -- ) 9 ex-sb sb-c ;
: ex-lf ( -- ) 10 ex-sb sb-c ;
: ex-sections ( elf -- ) { elf }
  bts @ 7 + 8 / 1 max { bpw }
  sections om-used 0 ?do
    i sections om-live? if
      i sections om-key { na nu }
      elf if
        na nu s" .text" str=cs if s" AX" else na nu s" .data" str=cs if s" WA" else s" " then then
      else s" " then { fa fu }
      na nu sec-ranges-of dup 0= if drop 1 then 0 ?do
        na nu i sec-range@ { rs rl }
        na nu ex-sb sb+  ex-tab
        rs bpw * ex-hex  ex-tab  rl bpw * ex-hex  ex-tab
        fa fu ex-sb sb+  ex-lf
      loop
    then
  loop ;
: ex-labels ( elf -- ) { elf }
  bts @ 7 + 8 / 1 max { bpw }
  export-labels om-used 0 ?do
    i export-labels om-live? if
      i export-labels om-key { na nu }
      i export-labels om-val { sl }
      sl qundef-derived? 0= if
        sl 6 cells + @ if sl else sl bpw qn q* then { addr }
        na nu ex-sb sb+
        elf if
          na nu lab-find ?dup if
            lab-rtype dup 0>= if mt-rev@ dup if s" ::" ex-sb sb+ ex-sb sb+ else 2drop then else drop then
          then
        then
        ex-tab addr ex-hexq ex-lf
      then
    then
  loop ;
: ex-errno ( ior -- n ) dup -512 <= if 512 + negate else drop 2 then ;
: write-export ( pa pu elf -- ok ) { pa pu elf }
  ex-sb sb-clear
  elf ex-sections  elf ex-labels
  pa pu w/o create-file { fid ior }
  ior 0<> if
    ior ex-errno { en }
    mb-reset s"  error - cannot write '" mb+ pa pu mb+ s" ': [Errno " mb+ en mb-n s" ] " mb+ en errno-text mb+
    s" : '" mb+ pa pu mb+ s" '" mb+ mb-get diag-e false exit
  then
  ex-sb sb$ fid write-file drop
  fid close-file drop
  true ;
: write-exports-impl ( -- ok )
  o-exp-u @ if o-exp-a @ o-exp-u @ false write-export 0= if false exit then then
  o-expe-u @ if o-expe-a @ o-expe-u @ true write-export 0= if false exit then then
  true ;
' write-exports-impl is write-exports

\ -o と -b を同時に使ったときの警告 (axx.py write の _zeroed)
: raw-zero-warn-impl ( -- )
  o-obj-u @ 0= if exit then
  mt-rela? { rela }
  0 { nz }  mb-reset
  rl-n @ 0 ?do
    rela if true else i rl@ 5 cells + @ mt-field? if 2drop 2drop true else false then then
    if
      nz 1+ to nz
      nz 5 < if
        nz 1 > if s" , " mb+ then
        i rl@ dup @ swap cell+ @ mb+  s" +0x" mb+ i rl@ 2 cells + @ qn false q>hex mb+
      then
    then
  loop
  nz 0= if exit then
  nz 4 > if s" , ..." mb+ then
  mb-get sdup { wa wu }
  mb-reset s"  warning - " mb+ nz mb-n s"  field(s) were left 0 for the linker (" mb+ wa wu mb+
  s" ); this raw binary is only correct after linking " mb+ o-obj-a @ o-obj-u @ mb+
  s" . Drop -o to have axx fill them in." mb+ mb-get diag-wf ;
' raw-zero-warn-impl is raw-zero-warn

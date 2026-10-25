0 constant cc-forth
\ ccshim.fs -- ccforth (Forth→C コンパイラ) 用の補い。gforth では読み込まない。
\ gforth 固有の語のうち ccforth に無いものをここで定義する。

0 constant stdin
1 constant stdout
2 constant stderr
: bounds ( a u -- a+u a ) over + swap ;
: f> ( f: a b -- ) ( -- f ) fswap f< ;
: f<= ( f: a b -- ) ( -- f ) f> 0= ;
: f>= ( f: a b -- ) ( -- f ) f< 0= ;
: f<> ( f: a b -- ) ( -- f ) f= 0= ;
: l! ( u a -- ) over 255 and over c! over 8 rshift 255 and over 1+ c!
  over 16 rshift 255 and over 2 + c! swap 24 rshift 255 and swap 3 + c! ;
: ul@ ( a -- u ) dup c@ over 1+ c@ 8 lshift or over 2 + c@ 16 lshift or swap 3 + c@ 24 lshift or ;
: get-dir ( a u -- a u' ) { a u }
  s" PWD" getenv dup 0= if 2drop s" /" then u min { sa su }
  sa a su move a su ;
CODE (BYE) n --
  exit((int)p0);
;CODE
: off ( a -- ) 0 swap ! ;
: on ( a -- ) -1 swap ! ;

\ ---- 遅延語 (defer / bind) ----
\ ccforth の DEFER はインタプリタ専用で、C にできない。ここでは本体の先頭に実行トークンを
\ 持つ語として作り、`bind` は実行時に結ぶ語 (_bN) を作る。_bN は最後に bind-all から呼ぶ。
: defer ( "name" -- )
  parse-name { na nu }
  s" 0 value " na nu s+ s" -xt" s+ evaluate
  s" : " na nu s+ s"  " s+ na nu s+ s" -xt execute ;" s+ evaluate ;
variable bcount
create bsrc 65536 allot
variable bsrc-n
: bsrc+ ( a u -- ) dup >r bsrc bsrc-n @ + swap move r> bsrc-n +! ;
: num>s ( n -- a u ) s>d <# #s #> ;
: bind ( "impl" "target" -- )
  parse-name { ia iu }  parse-name { ta tu }
  1 bcount +!
  s" _b" bcount @ num>s s+ { na nu }
  s" : " na nu s+ s"  ['] " s+ ia iu s+ s"  to " s+ ta tu s+ s" -xt ;" s+ evaluate
  s"  " bsrc+  na nu bsrc+ ;
: finish-binds ( -- )
  s" : bind-all " bsrc bsrc-n @ s+ s"  ;" s+ evaluate ;
16 allocate throw constant cc-dummy-alloc

\ 標準入出力 (ccforth のファイル番号 0〜2 は実ファイルに結びついていないので C で直接書く)
CODE ETYPE a u --
  fwrite((void*)(uintptr_t)p0, 1, (size_t)p1, stderr);
;CODE
CODE STDIN-READ a u -- n n
  size_t _n = fread((void*)(uintptr_t)p0, 1, (size_t)p1, stdin);
  r0 = (cell_t)_n; r1 = 0;
;CODE
CODE STDIN-LINE a u -- n n n
  size_t _n = 0; int _c = 0, _got = 0;
  while ((cell_t)_n < p1 && (_c = getc(stdin)) != EOF) {
    _got = 1;
    if (_c == '\n') break;
    ((unsigned char*)(uintptr_t)p0)[_n++] = (unsigned char)_c;
  }
  r0 = (cell_t)_n; r1 = _got ? -1 : 0; r2 = 0;
;CODE
CODE STDOUT-FLUSH -- n
  #include <errno.h>
  if (fflush(stdout) != 0) return -512 - (cell_t)errno;
  return 0;
;CODE

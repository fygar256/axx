\ match4.fs -- 照合 (続き): .sub の展開と 1 行の照合

decimal

: str-pos ( a u pa pu from -- idx ) { a u pa pu from }
  from u > if -1 exit then
  a from + u from - pa pu search if drop a - else 2drop -1 then ;
: vname-in ( a u k -- n ) { a u k } 0 { n }
  k u >= if 0 exit then
  a k + c@ lowc? 0= if 0 exit then
  1 to n
  begin k n + u < if a k n + + c@ dup lowc? over digc? or swap 95 = or else false then while n 1+ to n repeat
  n ;
: sub-find-ref ( a u from -- i end na nu va vu true | false ) { a u from } from { i } 0 0 0 { j k vl }
  begin
    a u s" !S{{" i str-pos to i
    i 0< if false exit then
    a u s" }}" i 4 + str-pos to j
    j 0< if false exit then
    i 0> if a i 1- + c@ 92 = else false then if
      j 2 + to i
    else
      j 2 + to k
      a u k vname-in to vl
      a i 4 + + j i 4 + - sub-name? vl 0> and if
        i  k vl +  a i 4 + + j i 4 + -  a k + vl  true exit
      then
      j 2 + to i
    then
  again ;


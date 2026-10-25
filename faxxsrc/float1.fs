\ float1.fs -- !F / !D の捕捉 (axx.py の !F !D、caxx.c の cap_float)

decimal

create fl-buf 16 allot
: f32-of ( q -- bits ok )                        \ 倍精度ビット列 -> 単精度ビット列
  dup qd-fin? { fin } qd fl-buf sf!
  fl-buf ul@ { b }
  fin b $7f800000 and $7f800000 = and if 0 false else b true then ;
: f64-of ( q -- bits ok ) @ true ;

: cap-fd ( kind -- ok ) { kind } 0 0 0 0 0 0 { n na stop sl st v }
  0 vname-at to n
  n 0= if false exit then
  mt-a @ ti @ + to na
  n ti +!
  0 var-stopchar to stop
  na n true vslot to sl
  false expr-missing !
  si @ to st
  ms-a @ ms-u @ si @ stop expr-esc-float si !  to v
  ncloses @ 0 ?do SUB-CLOSE i cells closes + @ sub-mark loop
  sl st si @ stop cap-text
  0 false { bits ok }
  v qundef? if 0 to bits true to ok else
    kind 70 = if v f32-of else v f64-of then to ok to bits
    ok 0= if
      kind 70 = if s"  error - !F: cannot convert value to float32; using 0."
      else s"  error - !D: cannot convert value to float64; using 0." then xerr
      0 to bits
    then
  then
  bits qun { bv }
  sl bv false false vput
  expr-missing @ if false exit then
  stop 0<> if 0 sc stop = if 1 si +! then then
  true ;


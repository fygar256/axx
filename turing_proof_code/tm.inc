!def tm_eval(rules, inp) {
!local W = 1
!local cur = 0
!local i = 0
!while i < len(rules) {
!if substr(rules, i, 1) == "+" !then {
!set cur = 0
} !else {
!set cur = cur + 1
!if cur > W !then {
!set W = cur
}
}
!set i = i + 1
}
!local T = ""
!local f = ""
!set i = 0
!while i <= len(rules) {
!if i == len(rules) || substr(rules, i, 1) == "+" !then {
!set T = T + substr("0" * W + f, len(f), W)
!set f = ""
} !else {
!set f = f + substr(rules, i, 1)
}
!set i = i + 1
}
!local tape = ""
!set i = 0
!while i < len(inp) {
!if substr(inp, i, 1) != "+" !then {
!set tape = tape + substr(inp, i, 1)
}
!set i = i + 1
}
!if len(tape) == 0 !then {
!set tape = "0"
}
!local n = len(T) / (5 * W)
!local q = 1
!local h = 0
!local c = 0
!local k = 0
!local w = 0
!while q != 0 {
!set c = int(substr(tape, h, 1), 10)
!set f = -1
!set k = 0
!while k < n {
!if int(substr(T, 5 * k * W, W), 10) == q && int(substr(T, (5 * k + 1) * W, W), 10) == c !then {
!set f = k
!break
}
!set k = k + 1
}
!if f < 0 !then {
!break
}
!set w = int(substr(T, (5 * f + 2) * W, W), 10)
!if w > 9 !then {
!error "tm: symbol must be 0..9"
}
!set tape = substr(tape, 0, h) + str(w) + substr(tape, h + 1)
!if int(substr(T, (5 * f + 3) * W, W), 10) == 0 !then {
!if h == 0 !then {
!set tape = "0" + tape
} !else {
!set h = h - 1
}
} !else {
!set h = h + 1
!if h == len(tape) !then {
!set tape = tape + "0"
}
}
!set q = int(substr(T, (5 * f + 4) * W, W), 10)
}
!local a = 0
!while a < len(tape) && substr(tape, a, 1) == "0" {
!set a = a + 1
}
!local b = len(tape)
!while b > a && substr(tape, b - 1, 1) == "0" {
!set b = b - 1
}
!return substr(tape, a, b - a)
}
!def tm_db(rules, inp) {
!local t = tm_eval(rules, inp)
!local i = 0
!while i < len(t) {
        .db !{int(substr(t, i, 1), 10)}
!set i = i + 1
}
}
!def tm_list(rules, inp) {
!local t = tm_eval(rules, inp)
!local s = ""
!local i = 0
!while i < len(t) {
!if i > 0 !then {
!set s = s + ","
}
!set s = s + substr(t, i, 1)
!set i = i + 1
}
!if len(s) == 0 !then {
!set s = ";;0"
}
!return s
}

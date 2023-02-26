let input = \s.\z.s(s(s(s(s(s(s(s z))))))) in
let one = \s.s in
let mul = \m.\n.\f.(m (n f)) in
let prec = \n.\f.\x. n (\g.\h. h (g f)) (\u.x) (\u.u) in
let T = \x.\y.x in
let F = \x.\y.y in
let if0 = \m.m (\n.F) T in
let fact = \f.\n.((if0 n) one (mul n (f (prec n)))) in
let Y = \f.(\x.f(x x))(\x.f(x x)) in
Y fact input

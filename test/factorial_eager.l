let x = \s.\z.s(s(s z)) in
let one = \x.x in
let mul = \m.\n.\f.(m (n f)) in
let prec = \n.\f.\x. n (\g.\h. h (g f)) (\u.x) (\u.u) in
let T = \x.\y.x in
let F = \x.\y.y in
let if0 = \m.m (\n.F) T in
let fact = \f.\n.((if0 n) one \v.mul n (f (prec n)) v) in
let Y = \f.(\x.f \v.x x v)(\x.f \v.x x v) in
let fact = Y fact in
(fact x) one

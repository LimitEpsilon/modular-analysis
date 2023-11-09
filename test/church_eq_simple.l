let true = \xT.\yT.xT in
let false = \xF.\yF.yF in

let plus = \p1.\p2.\pf.\x.p1 pf (p2 pf x) in

let mult = \m1.\m2.\mf.m2 (m1 mf) in

let pred = \n.\rf.\rx.
  n (\g.\h.h (g rf)) (\ignored.rx) (\id.id) in

let sub = \s1.\s2.s2 pred s1 in

let church0 = \f0.\x0.x0 in
let church1 = \f1.\x1.f1 x1 in
let church2 = \f2.\x2.f2 (f2 x2) in
let church3 = \f3.\x3.f3 (f3 (f3 x3)) in
let church_is0 = \z.z (\zx.false) true in

(* does not terminate *)
fix church_eq e1 = \e2.
  church_is0 e1
    (church_is0 e2 true false)
    (church_eq (sub e1 church1) (sub e2 church1)) in

church_eq church1 church1 false

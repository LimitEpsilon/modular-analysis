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

fix church_eq e1 = \e2.
  church_is0 e1
    (church_is0 e2 true false)
    (church_is0 e2 false
      (\eta.church_eq (pred e1) (pred e2) eta)) in

(* multiplication distributes over addition *)
church_eq
  (mult church2 (plus church1 church3))
  (plus (mult church2 church1) (mult church2 church3))
  church0

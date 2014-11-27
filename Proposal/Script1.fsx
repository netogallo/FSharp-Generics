#load "X:\Documents\Msc Thesis\Proposal\Proposal.fs"
module E = Proposal.TypeErassure

let l = E.Cons(1,E.Cons(2,E.Cons(3,E.Nil)));;
let p = E.P (1,2);;

E.incAll l;;
E.incAll p;;
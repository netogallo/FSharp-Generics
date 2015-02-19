type T() = class end
type A1<'x>(v : 'x) =
  inherit T()
  member o.X = v
type A2<'x>(v : 'x) =
  inherit T()
  member o.X = v

type OV() =
  member this.M1<'t when 't :> T>(x : A1<'t>) =
    printf "A1"

  member this.M1<'t when 't :> T>(x : A2<'t>) =
    printf "A2"

end

#load "X:\Documents\Msc Thesis\Proposal\Proposal.fs"
module E = Proposal.TypeErassure

let l = E.Cons(1,E.Cons(2,E.Cons(3,E.Nil)));;
let p = E.P (1,2);;

E.incAll l;;
E.incAll p;;

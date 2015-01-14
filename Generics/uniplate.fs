module Uniplate

[<AbstractClass>]
type Rep<'t>() =
  class

    member o.elem x =
      match x with
        | :? 't -> true
  end

  

let (|INT|_|) ((e : Rep<'t>),o) =
  match o with
    | :? 't as e' -> Some e'
    | _ -> None

// let (|Data|_|) (e : Rep) =
//   match e with
//     | INT _ -> None
//     | _ -> Some e


[<AbstractClass>]
type Rep() =
  class
  end

type RInt() =
  class
    inherit Rep()
  end
  

type Data<'t>() =
  class
    inherit Rep()
    abstract GetConstr : 't -> Rep*obj
  end


type Meta() =
  class
  end

type K() =
  class
    inherit Meta()
  end

type L() =
  class
    inherit Meta()
  end

type R() =
  class
    inherit Meta()
  end

type Prod() =
  class
    inherit Meta()
  end

type Id() =
  class
    inherit Meta()
  end

type U() =
  class
    inherit Meta()
  end

type D() =
  class
    inherit Meta()
  end


[<AbstractClass>]
type GSumR<'t>() =
  class

//    member o.gSum(meta:K, i:int) = i

    member o.gSum(meta:L, r:obj) =
      o.gSum(r)

    member o.gSum(meta:R, r:obj) =
      o.gSum(r)

    member o.gSum(meta:Prod, i:int, r:obj) =
      i + o.gSum(r)

    member o.gSum(meta:Id, r:'t) =
      o.gSum(r)

    member o.gSum(meta:U, ()) = 0

    member o.gSum(meta:D, x:obj) = 0

    // member o.gSum(r:Data<'t>,v:'t) =
    //   let (r',v') = r.GetConstr(v)
    //   match r' with
    //     :? RInt as r'' -> o.gSum(r'',v' :?> int)

    abstract gSum : obj -> int
  end
  
type AList<'t> = Cons of 't*AList<'t> | Nil

type AListP =
  { list : AList<int> }

type GSumImp() =
  class
    inherit GSumR<AList<int>>()

    override o.gSum(e : obj) =

      match e with
        | :? AList<int> as e' ->
          match e' with
            | Cons (x,xs) ->
              o.gSum(L(),{ list = Cons(x,xs) })
            | Nil -> o.gSum(U(),())
        | :? AListP as e' ->
          match e'.list with
            | Cons (x,xs) ->
              o.gSum(Prod(), x, (Id(),xs))
            | Nil ->
              o.gSum(U(), ())
        | :? (Id*AList<int>) as e' ->
          let (_,e'') = e'
          o.gSum(Id(),e'')
        | _ -> o.gSum(D(),e)

  end

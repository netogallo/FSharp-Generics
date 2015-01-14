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

[<AbstractClass>]
type Meta() =
  class
  end

[<AbstractClass>]
type Constr<'t>() =
  class
    inherit Meta()
  end

[<AbstractClass>]
type L<'t>() =
  class
    inherit Constr<'t>()
    abstract Constr : Constr<'t> -> Constr<'t>
  end

[<AbstractClass>]
type R<'t>() =
  class
    inherit Constr<'t>()
    abstract Constr : Constr<'t> -> Constr<'t>
  end

[<AbstractClass>]
type Prod<'t>() =
  class
    inherit Constr<'t>()
    abstract Prod : Constr<'t>*Constr<'t> -> Prod<'t>
  end

[<AbstractClass>]
type Id<'t>() =
  class
    inherit Constr<'t>()
    abstract Init : Constr<'t> -> Id<'t>
  end

[<AbstractClass>]
type K<'v,'t>() =
  class
    inherit Constr<'t>()
    abstract Init : 'v -> K<'v,'t>
  end

[<AbstractClass>]
type U<'t>() =
  class
    inherit Constr<'t>()
    abstract Create : unit -> U<'t>
  end

type D() =
  class
    inherit Meta()
  end

(*
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
*)
[<AbstractClass>]
type Everywhere<'t>() =

  member o.Everywhere(meta:L<'t>, r:obj,f:int -> int) =
    o.Everywhere(r,f) |> meta.Constr

  member o.Everywhere(meta:K<int,'t>, i:int,f:int -> int) =
    f i |> meta.Init

  member o.Everywhere(meta:Prod<'t>, i:obj, r:obj,f:int -> int) =
    meta.Prod(o.Everywhere(i,f),o.Everywhere(r,f))

  member o.Everywhere(meta:R<'t>, r:obj,f:int -> int) =
    o.Everywhere(r,f) |> meta.Constr

  member o.Everywhere(meta:U<'t>, u : unit, f:int->int) =
    meta

  member o.Everywhere(meta:Id<'t>, r:'t, f : int -> int) =
    o.Everywhere(r,f) |> meta.Init

  abstract Everywhere : obj*(int -> int) -> Constr<'t>
  
type AList<'t> = Cons of 't*AList<'t> | Nil

type AListP<'c> =
  {
    list : AList<int>
    meta : 'c
   }

type LConstr() =
  class
    inherit L<AList<int>>()
    let mutable (elem : Option<Constr<AList<int>>>) = None
    override o.Constr(e) =
      elem <- Some e
      o :> _
  end

type RConstr() =
  class
    inherit R<AList<int>>()
    let mutable (elem : Option<Constr<AList<int>>>) = None
    override o.Constr(e) =
      elem <- Some e
      o :> _
  end

type ProdConstr() =
  class
    inherit Prod<AList<int>>()
    let mutable (elem : Option<Constr<AList<int>>*Constr<AList<int>>>) = None
    override o.Prod(c1,c2) =
      elem <- Some(c1,c2)
      o :> _
  end


type KConstr() =
  class
    inherit K<int,AList<int>>()
    let mutable (v : Option<int>) = None
    override o.Init(x) =
      v <- Some x
      o :> _
  end

type UConstr() =
  class
    inherit U<AList<int>>()
    override o.Create() = UConstr() :> _
  end

type IdConstr() =
  class
    inherit Id<AList<int>>()
    let mutable (elem : Option<Constr<AList<int>>>) = None
    override o.Init(e) =
      elem <- Some e
      o :> _
  end
    

type EverywhereImp() =
  class
    inherit Everywhere<AList<int>>()

    override o.Everywhere(e:obj,f:int->int) =
      match e with
        | :? AList<int> as e' ->
          match e' with
            | Cons(_) -> o.Everywhere({list = e';meta = LConstr()},f)
            | Nil -> o.Everywhere({list = e';meta = RConstr()},f)
        | :? AListP<LConstr> as e' ->
          match e'.list with
            | Cons (x,xs) ->
              let (c : L<AList<int>>) = LConstr() :> _
              o.Everywhere(c,{list=Cons(x,xs);meta=ProdConstr()},f)
        | :? AListP<ProdConstr> as e' ->
          match e'.list with
            | Cons (x,xs) ->
              let (c : Prod<AList<int>>) = ProdConstr() :> _
              o.Everywhere(c,{list=Cons(x,xs);meta=KConstr()},{list=Cons(x,xs);meta=IdConstr()},f) :> _
        | :? AListP<KConstr> as e' ->
          match e'.list with
            | Cons (x,_) -> o.Everywhere(KConstr(),x,f) :> _
        | :? AListP<IdConstr> as e' ->
          match e'.list with
            | Cons (_,xs) -> o.Everywhere(IdConstr(),xs,f) :> _
            | Nil ->
              let (c : U<AList<int>>) = UConstr() :> _
              o.Everywhere(c,(),f) :> _
        | :? AListP<RConstr> as e' -> o.Everywhere(RConstr(),{list=Nil;meta=IdConstr()},f)
        | :? AListP<UConstr> -> o.Everywhere(UConstr(),(),f) :> _
      
  end

(*
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
*)

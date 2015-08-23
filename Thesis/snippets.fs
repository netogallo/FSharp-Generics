// adts.png
type List<'a> = Cons of 'a*List<'a>
  | Nil
  with
    member self.Length = match self with
      | Cons (_,xs) -> 1 + xs.Length
      | Nil -> 0

let head list = match list with
  | Cons (a,_) -> a
  | Nil -> failwith "Empty list"

// classes.png
[<AbstractClass>]
type Collection<'a>() =
  abstract Item : int -> 'a

type List<'a>(value' : 'a, next : Option<List<'a>>) = class
  inherit Collection<'a>()
  let mutable value = value'
  override self.Item i = if i = 0 then value else next.Value.Item (i - 1)
  member self.HasNext with get() = next.IsSome
  member self.Next with get() = next.Value
  member self.Value with get() = value
  and  set(newValue) = value <- newValue
  end

// boilerplate
let listTy = typeof<List<int>>
let constr = listTy.GetConstructor([| typeof<int>; typeof<Option<List<int>>> |])
constr.Invoke(null,[| 0; None |]) :?> List<int>

[<AbstractClass>]
type Meta() = class end

type U<'ty>() = inherit Meta()

type K<'ty,'x>(elem : 'x) =
  class
    inherit Meta()
    member self.Elem with
      get() = elem
  end

type Id<'ty>(elem : 'ty) =
  class
    inherit Meta()
    member self.Elem with
      get() = elem
  end

type Sum<'ty,'a,'b when 'a :> Meta
  and 'b :> Meta>(elem : Choice<'a,'b>) =
  class
    inherit Meta()
    member self.Elem with
    get() = elem
  end

type Prod<'ty,'a,'b when 'a :> Meta
  and 'b :> Meta>(e1 : 'a, e2 : 'b)=
  class
    inherit Meta()
    member self.Elem with get() = e1,e2
    member self.E1 with get() = e1
    member self.E2 with get() = e2
  end

// reflection.png
type List<'a> = Cons of 'a*List<'a> | Nil

[<Sealed>]
type List<'a> =
  type Cons<'a>(x : 'a, xs : List<'a>) =
    inherit List<'a>

  type Nil<'a>()= inherit List<'a>

type Generic<'a> =
  member From : 'a -> Meta
  member To : Meta -> 'a

[<AbstractClass>]
type Type =
  member GetNestedTypes : unit -> Type []
  member GetConstructor : Type [] -> ConstructorInfo

type FSharpType =
  static member GetUnionCases : Type -> UnionCaseInfo
  static member IsUnion : Type -> Bool


// foldmenta.png
[<AbstractClass>]
type FoldMeta<'t,'out>() =

  member FoldMeta : Meta*'in -> 'out
  
  abstract FoldMeta<'ty> : Sum<'ty,Meta,Meta> -> 'out
  abstract FoldMeta<'ty> : Prod<'ty,Meta,Meta> -> 'out
  abstract FoldMeta<'ty,'x> : K<'ty,'x> -> 'out
  abstract FoldMeta<'ty> : U<'ty> -> 'out
  abstract FoldMeta : Id<'t> -> 'out

// gmap.png

type GMap<'t,'a>(f : 'a -> 'a) =

  inherit FoldMeta<'t,Meta>()

  override self.FoldMeta<'ty>(sum : Sum<'ty,Meta,Meta>) =
    match sum.Elem with
    | Choice1Of2 s1 -> s1 |> self.FoldMeta
                          |> Choice1Of2
                          |> Sum<'ty,Meta,Meta>
    | Choice2Of2 s2 -> s2 |> self.FoldMeta
                          |> Choice2Of2
                          |> Sum<'ty,Meta,Meta>

  override self.FoldMeta<'ty>(prod : Prod<'ty,Meta,Meta>) =
    Prod<'ty,Meta,Meta>(self.FoldMeta prod.E1, self.FoldMeta prod.E2)

  override self.FoldMeta<'ty,'x>(k : K<'ty,'x>) = k

  member self.FoldMeta<'ty>(k : K<'ty,'a>) =
    k.Elem |> f |> K<'ty,'a>

  override self.FoldMeta<'ty>(u : U<'ty>) = u

  override self.FoldMeta(id : Id<'ty>) =
    let g = Generic<'t>()
    id.Elem |> g.From |> self.FoldMeta |> g.To |> Id<'ty>

// adhoc
type Prod<'t,'a,'b when 'a:(member GSum : int)
  and 'b:(member GSum : int) > with
  member self.GSum = self.E1.GSum + self.E2.GSum

type K<'t,'a> with
  abstract self.GSum : int
  override self.GSum = self.Elem

type K<'t,int> with
  override self.GSum = self.Elem

//extensible
type GMapShallow<'t,'a>(f : 'a -> 'a) =
  inherit GMap<'t,'a>(f)
  override self.GMap(id : Id<'t>) = id

//provider

type Nats = NatsProvider<10>

let zero = Nats.Zero() : Nats.Zero
let one = Nats.Succ() : Nats.Succ
let two = Nats.SuccSucc() :  Nats.SuccSucc

//mrec

type FoldMeta<'t,'out>() =
  member FoldMeta : Meta*Meta -> 'out

  abstract FoldMeta<'ty> : Sum<'ty,Meta,Meta> * Meta -> 'out
  abstract FoldMeta<'ty> : Prod<'ty,Meta,Meta> * Meta -> 'out
  abstract FoldMeta<'ty,'x> : K<'ty,'x> * Meta -> 'out
  abstract FoldMeta<'ty> : U<'ty> * Meta -> 'out
  abstract FoldMeta : Id<'t> * Meta -> 'out

type GEQ<'t>() =
  inherit FoldMeta<'t,bool>()

  override self.FoldMeta<'ty>(_ : Prod<'ty,Meta,Meta>, _ : Meta) = false
  member self.FoldMeta<'ty>(p1 : Prod<'ty,Meta,Meta>, p2 : Prod<'ty,Meta,Meta>) =
    self.FoldMeta(p1.E1, p2.E1) && self.FoldMeta(p1.E2, p2.E2)

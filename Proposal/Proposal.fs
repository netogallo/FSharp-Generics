module Proposal

module TypeErassure =

  type Tree<'a> = Leave of 'a | Branch of (Tree<'a>)*(Tree<'a>)

  type IGeneric =
    interface
    abstract map : (obj -> obj) -> obj
    abstract fold : (obj -> obj -> obj) -> obj -> obj
    end

  let gmap (t : 't when 't :> IGeneric) f = t.map f :?> IGeneric

  let gfold (t : 't when 't :> IGeneric) f s = t.fold f s

  type Sum<'t1,'t2 when 't1 :> IGeneric and 't2 :> IGeneric>(v : Choice<'t1,'t2>) =
    class
      member o.value with get() = v
      interface IGeneric with
        override x.map f =
          match v with
            | Choice1Of2 x ->
              let x' = x :> IGeneric
              Sum(Choice1Of2(gmap x' f)) :> IGeneric :> _
              | Choice2Of2 y ->
                let y' = y :> IGeneric
                in Sum(Choice2Of2(gmap y' f)) :> IGeneric :> _
        override x.fold f s =
          match v with
            | Choice1Of2 x ->
              let x' = x :> IGeneric
              in gfold x' f s
            | Choice2Of2 y ->
              let y' = y :> IGeneric
              in gfold y' f s
    end

  type K<'x>(v : 'x) =
    class
      member o.value with get() = v
      interface IGeneric with
        override x.map f =
          K(f v) :> IGeneric :> _
        override x.fold f s =
          f v s
    end

  type Prod<'t1,'t2 when 't1 :> IGeneric and 't2 :> IGeneric>(v : 't1*'t2) =
    class
      member o.value with get() = v
      interface IGeneric with
        override x.map f =
          let (a',b') = v
          let (a,b) = (a' :> IGeneric, b' :> IGeneric)
          Prod((gmap a f,gmap b f)) :> IGeneric :> _
        override x.fold f s =
          let (a,b) = (fst v :> IGeneric,snd v :> IGeneric)
          let s1 = gfold b f s
          gfold a f s1
    end

  type Unit() =
    class
      interface IGeneric with
        override x.map f = Unit() :> IGeneric :> _
        override x.fold f s = s
    end

  type IRegular =
    abstract from : unit -> IGeneric
    abstract toValue : IGeneric -> obj

    type Id<'t when 't :> IRegular>(x : 't) =
      class
        member o.value with get() = x
        interface IGeneric with
          override o.map f =
            let x' = gmap (x.from()) f
            let x'' = x.toValue x' :?> IRegular
            x.GetType() |> printf "%A\n"
            x''.GetType() |> printf "%A\n"
            let id' = Id(x'') :> IGeneric
            id' :> _
          override o.fold f s = gfold (x.from()) f s
            
      end

    type Pair = P of int*int with
      interface IRegular with
        override p.from() = 
          let (P (i,j)) = p
          Prod(K(i :> obj) :> IGeneric,K(j :> obj) :> IGeneric) :> _
        override p.toValue g =
          let (a,b) = (g :?> Prod<IGeneric,IGeneric>).value
          let (a',b') = ((a :?> K<obj>).value :?> int, (b :?> K<obj>).value :?> int)
          P (a',b') :> _

    type List<'a> = Cons of 'a*(List<'a>) | Nil with
      interface IRegular with
        override o.from() =
          match o with
            | Nil -> Sum(Choice2Of2(Unit() :> IGeneric)) :> _
            | Cons (x,xs) -> Sum(Choice1Of2(Prod(K(x :> obj) :> IGeneric,Id(xs :> IRegular) :> IGeneric) :> IGeneric)) :> _
        override o.toValue l =
          let rec listCast (xs : obj) =
            match xs with
                | :? List<obj> -> 
                    match (xs :?> List<obj>) with
                        | Nil -> Nil
                        | Cons (x,xs') -> Cons(x :?> 'a,listCast xs')
                | :? List<'a> -> 
                    match (xs :?> List<'a>) with
                        | Nil -> Nil
                        | Cons (x,xs') -> Cons(x,listCast xs')
          match (l :?> Sum<IGeneric,IGeneric>).value with
            | Choice1Of2 cons ->
              let (a,b) = (cons :?> Prod<IGeneric,IGeneric>).value
              let (a',b') = ((a :?> K<obj> ).value :?> 'a, (b :?> Id<IRegular>).value |> listCast)
              Cons (a',b') :> obj
            | Choice2Of2 nil -> Nil :> obj
      

    let incAll (x : IRegular) =
      let r = gmap (x.from()) (fun x -> (x :?> int) + 1 :> obj)
      x.toValue r

    let gsum (x : IRegular) =
      let r = gfold (x.from()) (fun x s -> (x :?> int) + (s :?> int) :> obj) (0 :> obj)
      r

    let list = Cons(1,Cons(2,Cons(3,Nil)))

module S =

  [<AbstractClass>]
  type Generic<'r>() =
    class
      abstract gmap : (int -> int) -> Generic<'r>
      abstract children : unit -> 'r list
      abstract parents : unit -> 'r list
    end

  type K<'r>(v : obj) =
    class
      inherit Generic<'r>()
      member o.value with get() = v
      override o.gmap f =
        match o.value with
          | :? int -> K(f (v :?> int) :> obj) :> _
          | _ -> K(v) :> _
      override o.children () = []
      override o.parents () = []
    end

  type Unit<'r>() =
    class
      inherit Generic<'r>()
      override o.gmap f = Unit<'r>() :> _
      override o.children () = []
      override o.parents () = []
    end

  type Prod<'a,'b,'r when 'a :> Generic<'r> and 'b :> Generic<'r>>(v : 'a*'b) =
    class
      inherit Generic<'r>()
      member o.value with get() = v
      override o.gmap f =
        let (a,b) = v
        let a' = a.gmap(f) // :> Generic<'r>
        let b' = b.gmap(f) // :> Generic<'r>
        Prod<_,_,_>(a',b') :> Generic<'r>
      override o.children () =
        let (a,b) = v
        let a' = a.children()
        let b' = b.children()
        List.concat [a'; b']
      override o.parents () =
        let (a,b) = v
        let a' = a.parents()
        let b' = b.parents()
        List.concat [a'; b']
    end

  type Sum<'a,'b,'r when 'a :> Generic<'r> and 'b :> Generic<'r>>(v : Choice<'a,'b>) =
    class
      inherit Generic<'r>()
      member o.value with get() = v
      override o.gmap f =
        match v with
          | Choice1Of2 v -> Sum<_,_,_>(Choice1Of2(v.gmap(f))) :> _
          | Choice2Of2 v -> Sum<_,_,_>(Choice2Of2(v.gmap(f))) :> _
      override o.children () =
        match v with
          | Choice1Of2 v -> v.children()
          | Choice2Of2 v -> v.children()
      override o.parents () =
        match v with
          | Choice1Of2 v -> v.parents()
          | Choice2Of2 v -> v.parents()
    end

  [<AbstractClass>]
  type Regular<'t>() =
    abstract from : 't -> Generic<'t>
    abstract toValue : Generic<'t> -> 't

  type Id<'r>(v,r : Regular<'r>) =
    class
      inherit Generic<'r>()
      member o.value with get() = v
      member o.rep with get () = r.from v
      override o.gmap f = Id(r.toValue(r.from(v).gmap(f)),r) :> _  // Id(f v,r) :> _
      override o.children () = [v]
      override o.parents () =
        match o.rep.children() with
          | [] -> []
          | _ -> v :: o.rep.parents()
    end

  type Pair = P of int*int

  type PairRep = Prod<K<int>,K<int>,int>

  type List<'t> = Cons of 't*List<'t> | Nil

  type LRegular() =
    class
      inherit Regular<List<int>>()
      override r.from o =
        match o with
          | Nil -> Sum<_,_,_>(Choice2Of2(Unit<_>() :> Generic<_>)) :> Generic<List<'x>>
          | Cons (x,xs) ->
            Sum<_,_,_>(Choice1Of2(Prod<_,_,_>(K(x) :> Generic<_>,Id(xs,r) :> Generic<_>) :> Generic<_>)) :> Generic<List<'x>>

      override r.toValue g' =
        match g' with
          | :? Sum<Generic<List<'t>>,Generic<List<'t>>,List<'t>> ->
            let g = g' :?> Sum<Generic<List<'t>>,Generic<List<'t>>,List<'t>>
            match g.value with
              | Choice1Of2 p' ->
                match p' with
                  | :? Prod<Generic<List<'t>>,Generic<List<'t>>,List<'t>> ->
                    let (a',b') = (p' :?> Prod<Generic<List<'t>>,Generic<List<'t>>,List<'t>>).value
                    let (a,b) = ((a' :?> K<List<'t>>).value, (b' :?> Id<List<'t>>).value)
                    Cons (a :?> int,b)
              | Choice2Of2 x ->
                x :?> Unit<List<'t>> |> ignore
                Nil
    end

  let lReg = LRegular()
  let aList = Cons(1,(Cons (2,Cons (3,Nil))))

S.lReg.toValue(S.lReg.from(S.aList).gmap(fun x -> x + 1)) //Adds 1 to every element of the list

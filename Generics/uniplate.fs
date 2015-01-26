namespace Generics

open System
open Microsoft.FSharp.Reflection

module Uniplate =
    let a = id

module Reflection =

    [<CustomComparison>]
    [<CustomEquality>]
    type TypeConstructor<'t> = {

        Info : UnionCaseInfo
        Matcher : 't -> bool
        Invoke : array<obj> -> 't
        Elems : 't -> (obj*System.Type) [] option
        Params : System.Type []
        }
        with
            member o.Cmp(o' : obj) =
                match o' with
                        | :? TypeConstructor<'t> as o'' -> 
                            compare (o.Info.Name,o.Info.Tag) (o''.Info.Name,o''.Info.Tag)
                        | _ -> 1
            override o.Equals(o') = o.Cmp(o') = 0
            interface IComparable with
                override o.CompareTo(o' : obj) = o.Cmp(o') 
                    

    type Microsoft.FSharp.Reflection.UnionCaseInfo with
        member x.Constructor with get() = 
            x.DeclaringType.GetMethods() 
            |> Array.find (fun mi -> mi.Name = sprintf "New%s" x.Name || mi.Name = sprintf "get_%s" x.Name)
        member x.Matcher with get() =
            x.DeclaringType.GetMethod(sprintf "get_Is%s" x.Name)

    let makeTypeConstructor<'t> (c : UnionCaseInfo) =
        let constr = c.Constructor
        let invoke args = constr.Invoke(null,args) :?> 't
        let matcher (o : 't) = c.Matcher.Invoke(o :> obj, [||]) :?> bool
        let getters =
            if c.DeclaringType.GetNestedType(c.Name) = null then
                [||]
            else
                let ct = 
                    if c.DeclaringType.GetNestedType(c.Name).ContainsGenericParameters then
                        c.DeclaringType.GetNestedType(c.Name).MakeGenericType c.DeclaringType.GenericTypeArguments
                    else
                        c.DeclaringType.GetNestedType(c.Name)
                ct.GetMethods() |> Array.filter (fun mi -> mi.Name.Contains "get_Item")
            
        let elems (o : 't) =
            if matcher o then
                getters |> Array.map (fun g -> g.Invoke(o,[||])) 
                        |> Array.zip (c.GetFields() |> Array.map (fun fi -> fi.PropertyType)) 
                        |> Array.map (fun (a,b) -> (b,a)) |> Some
            else
                None
        {
            Info = c
            Matcher = matcher
            Invoke = invoke
            Elems = elems
            Params = getters |> Array.map (fun m -> m.ReturnType)
        }


module Rep =

    [<AbstractClass>]
    type Meta() =
      class
        abstract Values : seq<obj> with get
      end

    [<AbstractClass>]
    type Constr() =
        class
            inherit Meta()
            abstract Childs : Meta seq with get
        end

    [<AbstractClass>]
    type Constr<'t>() =
      class
        inherit Constr()
      end
   
        // :?> Constr<'t>
    type Constr with
        member o.Everywhere<'a when 'a :> Meta>(a : 'a, f : int -> int) = obj() :?> 'a

    [<Interface>]
    type SumConstr =
        interface
            abstract member SumValue : SumConstr option
        end

    [<AbstractClass>]
    type SumConstr<'a,'b when 'a :> Meta and 'b :> Meta>() =
        class
            inherit Constr<Choice<'a,'b>>()
            abstract Sum : Choice<'a,'b> with get
            // abstract Elem : Choice<'a,'b> with get
            // interface SumConstr
        end

        

    type L<'a,'b when 'a :> Meta and 'b :> Meta>(elem : 'a) =
      class
        inherit SumConstr<'a,'b>()
        member o.Elem with get() = elem
        override o.Sum with get() = elem |> Choice1Of2
        override o.Childs with get() = seq [elem]
        override o.Values with get() = elem.Values 
      end

    type L<'a,'b when 'a :> Meta and 'b :> Meta> with
        member o.Everywhere(f) = L<'a,'b>(o.Everywhere<'a>(o.Elem,f))

    // type L2<'c,'t>(elem : 't) = class end

    type R<'a,'b when 'a :> Meta and 'b :> Meta>(elem : 'b) =
      class
        inherit SumConstr<'a,'b>()
        member o.Elem with get() = elem
        override o.Sum with get() = elem |> Choice2Of2
        override o.Childs with get() = seq [elem]
        override o.Values with get() = elem.Values
      end
    
    type R<'a,'b when 'a :> Meta and 'b :> Meta> with
        member o.Everywhere(f) = R<'a,'b>(o.Everywhere<'b>(o.Elem,f))

    type Prod<'a,'b when 'a :> Meta and 'b :> Meta>(elem : 'a*'b) =
      class
        inherit Constr<'a*'b>()
        let (e1,e2) = elem
        member o.Elem with get() = elem
        override o.Childs with get() = seq [e1;e2] 
        override o.Values with get() = 
            let (a,b) = elem
            Seq.concat [a.Values;b.Values]
      end
    
    type Prod<'a,'b> with
        member o.Everywhere(f) =
            let (a,b) = o.Elem
            Prod(o.Everywhere<'a>(a,f),o.Everywhere<'b>(b,f))

    type Id<'t>(elem : 't) =
      class
        inherit Meta()
        member o.Elem with get() = elem
        override o.Values with get() = [elem :> obj] |> seq
      end
    
    type K<'v>(elem : 'v) =
      class
        inherit Meta()
        member o.Elem with get() = elem
        override o.Values with get() = [elem :> obj] |> seq
      end

    type K<'v> with
        member o.Everywhere(f) = K(f o.Elem)
    
    type U() =
      class
        inherit Meta()
        override o.Values with get() = Seq.empty
      end

    type U with
        member o.Everywhere(f) = U() 
   
    let pmatch t' (o : Meta) =
       try
            let t = o.GetType().GetGenericTypeDefinition().MakeGenericType([|typeof<Meta>;typeof<Meta>|])
            // let t' = typeof<L<U,U>>
            if t.IsSubclassOf t' || t = t' then
                o.GetType().GetProperty("Elem").GetValue(o) :?> Meta |> Some
            else None
        with
            | :? System.InvalidOperationException -> None

    let (|L|_|) (o : Meta) = pmatch typeof<L<Meta,Meta>> o
    let (|R|_|) (o : Meta) = pmatch typeof<R<Meta,Meta>> o

    let (|SUM|_|) (o : Meta) =
        match o with
            | L x -> Choice1Of2 x |> Some
            | R x -> Choice2Of2 x |> Some
            | _ -> None

    let (|PROD|_|) (o : Meta) =
        try
            let t = o.GetType().GetGenericTypeDefinition().MakeGenericType([|typeof<Meta>;typeof<Meta>|])
            let t' = typeof<Prod<Meta,Meta>>
            if t.IsSubclassOf t' || t = t' then
                let v = o.GetType().GetProperty("Elem").GetValue(o)
                let e1 = v.GetType().GetProperty("Item1").GetValue(v)
                let e2 = v.GetType().GetProperty("Item2").GetValue(v)
                (e1 :?> Meta, e2 :?> Meta) |> Some
            else
                None
        with
            | :? System.InvalidOperationException -> None
            | :? System.ArgumentException -> None

    let rec expand (o : Meta) =
        match o with
            | PROD (e1,e2) -> e1 :: expand e2
            | _ -> [o]

    let (|ID|_|) (o : Meta) =
        try
            let t = o.GetType().GetGenericTypeDefinition().MakeGenericType([|typeof<obj>|])
            let t' = typeof<Id<obj>>
            if t.IsSubclassOf t' || t = t' then
                o.GetType().GetProperty("Elem").GetValue(o) |> Some
            else
                None
        with
            | :? System.InvalidOperationException -> None
            | :? System.ArgumentException -> None

    let (|K|_|) (o : Meta) =
        try
            let t = o.GetType().GetGenericTypeDefinition().MakeGenericType([|typeof<obj>|])
            let t' = typeof<K<obj>>
            if t.IsSubclassOf t' || t = t' then
                o.GetType().GetProperty("Elem").GetValue(o) |> Some
            else
                None
        with
            | :? System.InvalidOperationException -> None
            | :? System.ArgumentException -> None

    let (|U|_|) (o : Meta) =
        try
            let t = o.GetType()
            let t' = typeof<U>
            if t.IsSubclassOf t' || t = t' then
                Some ()
            else
                None
        with
            | :? System.InvalidOperationException -> None

    type Generic<'t>() =
        
        let cases =  
            if Reflection.FSharpType.IsUnion typeof<'t> then
                Reflection.FSharpType.GetUnionCases typeof<'t> |> Array.map Reflection.makeTypeConstructor<'t>
            else
                [||]

        let (_,unions,matches) = 
            let cata (constr,unions,matchers) uc = 
                let t = constr(U() :> Meta).GetType()
                ((fun e -> R(constr e) :> Meta),Map.add uc constr unions,List.concat [matchers;[(t,uc)]])
            cases 
            |> Array.fold cata ((fun x -> L(x) :> Meta),Map.empty,[])

        member o.Construct (e:Constr) (tc : Reflection.TypeConstructor<'t>) = e.Values |> Seq.toArray |> tc.Invoke

        member o.Build(args : (obj*Type) []) =
            let cata (e,t') prod =
                //let t' = e.GetType()
                let t1 = prod.GetType()
                let gProd = typeof<Prod<Meta,Meta>>.GetGenericTypeDefinition()
                let mkType t2 elem =
                    let tProd = gProd.MakeGenericType([|t2;t1|])
                    let tup = typeof<Tuple<obj,obj>>.GetGenericTypeDefinition().MakeGenericType([| t2;t1 |])
                    let constr = tProd.GetConstructor([| tup |])
                    constr.Invoke([| tup.GetConstructor([| t2;t1 |]).Invoke([| elem;prod |]) |]) :?> Meta
                if typeof<'t> = t' then
                    let t2 = typeof<Id<'t>>
                    let v = t2.GetConstructor([| typeof<'t> |]).Invoke([| e |])
                    v |> mkType t2
                else
                    let t2 = typeof<Generic<obj>>.GetGenericTypeDefinition().MakeGenericType([| t' |])
                    let g' = t2.GetConstructor([||]).Invoke([||])
                    let v = g'.GetType().GetMethod("To").Invoke(g',[|e|]) :?> Meta
                    v |> mkType (v.GetType())
                    (*
                    let t2 = typeof<K<obj>>.GetGenericTypeDefinition().MakeGenericType([| t' |])
                    let v = t2.GetConstructor([| t' |]).Invoke([| e |])
                    v |> mkType t2
                    *)
            Array.foldBack cata args (U() :> Meta)


        member o.Constructor(e : 't) = cases |> Array.find (fun c -> c.Matcher e)


        member o.MatchRep(e : Constr) = 
        
            let cata (m,constr : Constr) (tc : Reflection.TypeConstructor<'t>) =
                match (m,constr) with
                    | (Some _,_) -> (m,constr)
                    | (None, L v) -> (Some tc, v :?> Constr)
                    | (None, R v) when v.GetType().IsSubclassOf(typeof<Constr>) -> (None, v :?> Constr)
                    | _ -> Exception(sprintf "Invalid representation: The representation '%A' does not match a constructor of type %s" e (typeof<'t>.ToString())) |> raise

            match matches |> Seq.map (fun (_,x) -> x) |> Seq.fold cata (None,e) with
                | (Some c,constr) -> (c,constr)
                | _ -> Exception(sprintf "Invalid representation: The representation '%A' does not match a constructor of type %s" e (typeof<'t>.ToString())) |> raise

        member o.From(r : Meta) = 
            match r with
                | :? Constr as r' -> 
                    let (c,constr) = o.MatchRep r'
                    let builder (t,(m : Meta)) =
                        match m with
                            | ID l -> l
                            | _ -> 
                                let b = typeof<Generic<obj>>.GetGenericTypeDefinition().MakeGenericType([| t |]).GetConstructor([||]).Invoke([||])
                                b.GetType().GetMethod("From").Invoke(b,[|m|])
                    expand constr |> Seq.zip c.Params |> Seq.map builder |> Seq.toArray |> c.Invoke
                | K v -> v :?> 't
                | _ -> Exception(sprintf "Invalid representation '%A' for '%s'" r (typeof<'t>.ToString())) |> raise

        member o.To(a : 't) =  
            let t = typeof<'t>
            if Reflection.FSharpType.IsUnion t then
                let c = o.Constructor a
                let mkRep = Map.find c unions
                match c.Elems a with
                    | Some es -> es |> o.Build |> mkRep

                // let unions = 
                // Constr()
            else
                K<'t>(a) :> _
                //Exception("Not an ADT") |> raise
 
    type Id<'t> with
        member o.Everywhere(f) = 
            let g = Generic<'t>()
            let c = g.To o.Elem
            Id(c.Everywhere(c,f) |> g.From)
    (*
    type D() =
      class
        inherit Meta()
      end
    *)
    // type 

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
    

    [<AbstractClass>]
    type Everywhere<'c,'t, 'u when 'c :> Constr<'t> and 't :> Constr<'u>>() =
    
      member o.Everywhere(meta:L<'t,'u>, r:obj,f:int -> int) =
        L(o.Everywhere(meta.Elem,f)) :> Constr<'t>
   
    
      member o.Everywhere<'u>(meta:R<'t>, r:obj,f:int -> int) =
        R(o.Everywhere(r,f))

      member o.Everywhere(meta:K<int,'t>, i:int,f:int -> int) =
        K(f i)
    
      member o.Everywhere(meta:Prod<'t>, i:obj, r:obj,f:int -> int) =
        Prod(o.Everywhere(i,f),o.Everywhere(r,f))
    
    
      member o.Everywhere(meta:U<'t>, u : unit, f:int->int) =
        meta
    
      member o.Everywhere(meta:Id<'t>, r:'t, f : int -> int) =
        Id(o.To(o.Everywhere(r,f)))
    
      abstract Everywhere : 't*(int -> int) -> 't
      
      // abstract To : Constr<'t> -> 't
      *)
    type AList<'t> = Cons of 't*AList<'t> | Nil
    
    type AListP<'c> =
      {
        list : AList<int>
        meta : 'c
       }        

(*
    type EverywhereImp() =
      class
        inherit Everywhere<AList<int>>()

        let constrs = FSharpType.GetUnionCases typeof<AList<int>> |> Array.map Reflection.makeTypeConstructor 

        let (_,sums) = 
            constrs 
            |> Array.fold (fun (constr,mappings) e -> ((fun e' -> (R(constr e') :> Constr<_>)), mappings |> Map.add e constr)) ((fun e -> (L(e) :> Constr<_>)), Map.empty)
        override o.Everywhere(e:obj,f:int->int) =

            match e with
                | :? AList<int> as e' ->
                    let c = constrs |> Array.find (fun c -> c.Matcher e')
                    \ 
            

          match e with
            | :? AList<int> as e' ->
              Microsoft.FSharp.Reflection.FSharpType.
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
    
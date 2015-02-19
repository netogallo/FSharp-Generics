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
        abstract Childs : Meta seq with get
        abstract Cast : unit -> Meta
        member x.GenericInit types args =
            let t = x.GetType().GetGenericTypeDefinition().MakeGenericType(types)
            let argValues,argTypes = Array.unzip args
            let c = t.GetConstructor(argTypes)
            if c = null then
                sprintf "No constructor of %s for args %A found" t.FullName args |> failwith
            else
                c.Invoke(argValues) :?> Meta
      end

    (*
    [<AbstractClass>]
    type Constr() =
        class
            inherit Meta()
            abstract Childs : Meta seq with get
        end
    *)
    
    [<AbstractClass>]
    type Constr<'t>() =
      class
        inherit Meta()
      end
   
        // :?> Constr<'t>
    
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
        override o.Cast() = L<Meta,Meta>(elem) :> _
      end

    // type L2<'c,'t>(elem : 't) = class end

    type R<'a,'b when 'a :> Meta and 'b :> Meta>(elem : 'b) =
      class
        inherit SumConstr<'a,'b>()
        member o.Elem with get() = elem
        override o.Sum with get() = elem |> Choice2Of2
        override o.Childs with get() = seq [elem]
        override o.Values with get() = elem.Values
        override o.Cast() = R<Meta,Meta>(elem) :> _
      end
    

    type Prod<'a,'b when 'a :> Meta and 'b :> Meta>(elem : 'a*'b) =
      class
        inherit Constr<'a*'b>()
        let (e1,e2) = elem
        member o.Elem with get() = elem
        member o.E1 with get() = e1
        member o.E2 with get() = e2
        override o.Childs with get() = seq [e1;e2] 
        override o.Values with get() = 
            let (a,b) = elem
            Seq.concat [a.Values;b.Values]
        override o.Cast() = 
            let a,b = elem
            Prod<Meta,Meta>(a :> _, b :> _) :> _
      end

    type Id<'t>(elem : 't) =
      class
        inherit Constr<'t>()
        member o.Elem with get() = elem
        override o.Values with get() = [elem :> obj] |> seq
        override o.Childs with get() = Seq.empty
        override o.Cast() = o :> _
      end
            
    
    type K<'v when 'v :> obj>(elem : 'v) =
      class
        inherit Constr<'v>()
        member o.Elem with get() = elem
        override o.Values with get() = [elem :> obj] |> seq
        override o.Childs with get() = Seq.empty
        override o.Cast() = o :> _
      end

    type U() =
      class
        inherit Constr<unit>()
        override o.Values with get() = Seq.empty
        override o.Childs with get() = Seq.empty
        override o.Cast() = o :> _
      end
   
    let pmatch t' (o : Meta) =
       try
            let t = o.GetType().GetGenericTypeDefinition().MakeGenericType([|typeof<Meta>;typeof<Meta>|])
            // let t' = typeof<L<U,U>>
            if t.IsSubclassOf t' || t = t' then
                o.GetType().GetProperty("Elem").GetValue(o) :?> Meta |> Some
            else None
        with
            | :? System.InvalidOperationException -> None
            | :? System.ArgumentException -> None

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

        member o.Construct (e:Meta) (tc : Reflection.TypeConstructor<'t>) = e.Values |> Seq.toArray |> tc.Invoke

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


        member o.MatchRep(e : Meta) = 
        
            let cata (m,constr : Meta) (tc : Reflection.TypeConstructor<'t>) =
                match (m,constr) with
                    | (Some _,_) -> (m,constr)
                    | (None, L v) -> (Some tc, v)
                    | (None, R v) when v.GetType().IsSubclassOf(typeof<Meta>) -> (None, v :?> Meta)
                    | _ -> Exception(sprintf "Invalid representation: The representation '%A' does not match a constructor of type %s" e (typeof<'t>.ToString())) |> raise

            match matches |> Seq.map (fun (_,x) -> x) |> Seq.fold cata (None,e) with
                | (Some c,constr) -> (c,constr)
                | _ -> Exception(sprintf "Invalid representation: The representation '%A' does not match a constructor of type %s" e (typeof<'t>.ToString())) |> raise

        member o.From(r' : Meta) = 
            match r' with
                | K v -> v :?> 't
                | _ -> 
                    let (c,constr) = o.MatchRep r'
                    let builder (t,(m : Meta)) =
                        match m with
                            | ID l -> l
                            | _ -> 
                                let b = typeof<Generic<obj>>.GetGenericTypeDefinition().MakeGenericType([| t |]).GetConstructor([||]).Invoke([||])
                                b.GetType().GetMethod("From").Invoke(b,[|m|])
                    expand constr |> Seq.zip c.Params |> Seq.map builder |> Seq.toArray |> c.Invoke
                // | _ -> Exception(sprintf "Invalid representation '%A' for '%s'" r (typeof<'t>.ToString())) |> raise

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

    type Meta with
        member o.Everywhere<'t>(f : int -> int) = 
            let t = o.GetType()
            let m = t.GetMethod("Everywhere", [|f.GetType()|])
            if m.ContainsGenericParameters then
                m.MakeGenericMethod([|typeof<'t>|]).Invoke(o,[|f|]) :?> 't
            else
                m.Invoke(o,[|f|]) :?> 't
        // (System.Exception("") |> raise) : 't

    type L<'a,'b when 'a :> Meta and 'b :> Meta> with
        static member Everywhere(o : L<'a,'b>, f : int -> int) = L<'a,'b>(o.Elem.Everywhere<'a>(f))

    type R<'a,'b when 'a :> Meta and 'b :> Meta> with
        static member Everywhere(o : R<'a,'b>, f : int -> int) = R<'a,'b>(o.Elem.Everywhere<'b>(f))

    type K<'v> with
        static member Everywhere(o : K<int>, f : int -> int) = K(f o.Elem)
        static member Everywhere(o : K<'v>, f : int -> int) = o

    type U with
        static member Everywhere(o : U, f : int -> int) = o
 
    type Id<'t> with
        static member Everywhere(o : Id<'t>, f : int -> int) =
            let g = Generic<'t>()
            Id<'t>(g.To(o.Elem).Everywhere<Meta>(f) |> g.From)

    type Prod<'a,'b when 'a :> Meta and 'b :> Meta> with
        static member Everywhere(o : Prod<'a,'b>, f : int -> int) =
            Prod<'a,'b>((o.E1.Everywhere<'a>(f),o.E2.Everywhere<'b>(f)))    

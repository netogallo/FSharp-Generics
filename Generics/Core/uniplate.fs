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

        member x.Matches(o) =
          x.Matcher.Invoke(o,[||])
          
    [<AbstractClass>]
    type TyAlg<'t,'s>() =
      abstract Id : int*Type -> 's
      abstract Case : int*(UnionCaseInfo*'s[])[] -> 's
      abstract Prim : int*Type -> 's
      
    let foldType<'t,'s> (alg : TyAlg<'t,'s>) =
      let count = ref 0
      let inc() = count := !count + 1;!count
      let rec fold ty =
        let i = inc()
        if ty = typeof<'t> then
          alg.Id(i,ty)
        elif Reflection.FSharpType.IsUnion ty then
          unions i ty
        else
          alg.Prim(i,ty)
      and unions i ty =
        let uns =
            Reflection.FSharpType.GetUnionCases ty
            |> Array.map (fun uc -> (uc,uc.GetFields()
                                    |> Array.map (fun pi -> pi.PropertyType)
                                    |> Array.map fold))
        alg.Case(i,uns)
      unions (inc()) typeof<'t>
          
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
    

    type Prod<'a,'b when 'a :> Meta and 'b :> Meta>(e1:'a, e2:'b) =
      class
        inherit Constr<'a*'b>()
        member o.Elem with get() = e1,e2
        member o.E1 with get() = e1
        member o.E2 with get() = e2
        override o.Childs with get() = seq [e1;e2] 
        override o.Values with get() = 
            Seq.concat [e1.Values;e2.Values]
        override o.Cast() = 
            Prod<Meta,Meta>(e1 :> Meta, e2 :> Meta) :> _
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


    type GTree<'t> =
      | Prim of (obj -> Meta)
      | Self of ('t -> Meta)
      | UC of ((GTree<'t> [])*UnionCaseInfo*(Meta[] -> Meta)) []

    [<AbstractClass>]
    type ValAlg<'t,'s>() =
      abstract Id : int*('t -> Meta)*'t -> 's
      abstract Case : int*Reflection.UnionCaseInfo*(Meta[] -> Meta)*('s[]) -> 's
      abstract Prim : int*(obj -> Meta)*obj -> 's

(*
    let foldVal<'t,'s> (t' : GTree<'t>) (alg : ValAlg<'t,'s>) (x : 't) =
      let count = ref 0
      let inc() = count := !count + 1;!count
      let rec fold' (t : GTree<'t>) (v : obj) =
        let i = inc()
        match t with
        | Prim c -> alg.Prim(i,c,v)
        | Self c -> alg.Id(i,c,v :?> 't)
        | UC ucs ->
          let ty = v.GetType()
          let (gts,uc,c) = ucs |> Array.find (fun (_,uc,_) -> u.Matches v)
          let prev = Reflection.FSharpValue.GetUnionFields(v,ty)
                     |> (fun (_,objs) -> Array.zip gts objs)
                     |> Array.map (fun (gt,(_,o)) -> fold' gt o)
          alg.Case(i,uc,c,prev)
      fold' t' x
*)
    type RepTypeAlg<'t>() =
      inherit Reflection.TyAlg<'t,GTree<'t>>()

      override this.Id(i,ty) = Self(fun v -> Id<'t>(v) :> _)

      override this.Case(i,cases) =

        let pTy = typeof<Prod<Meta,Meta>>.GetGenericTypeDefinition()

        // Function to pack the constituents of a type constructor into a
        // sequential application of the Prod constructor
        let mkCase tys =
          let (tf,constrs) =
            Array.foldBack (fun ty (t,s) ->
              let t' = pTy.MakeGenericType [| ty;t |]
              let c = t'.GetConstructor [| ty;t |]
              (t', c::s)) tys (typeof<U>,[])
            |> fun (tf,cs) -> (tf,Array.ofList cs)
          let mk (ms : Meta []) =
            Array.foldBack (fun (c : Reflection.ConstructorInfo,v) s ->
                            c.Invoke [|v;s|]) (Array.zip constrs ms) (U() :> obj) :?> Meta
          (tf, mk)

        let sTy = typeof<SumConstr<Meta,Meta>>.GetGenericTypeDefinition()           
        let caseCata (uc : UnionCaseInfo,vals) ((ty,tf,c)::xs) =
          let (tf',c') = uc.GetFields()
                       |> Array.map (fun pi -> pi.PropertyType)
                       |> mkCase
          let ty' = sTy.MakeGenericType [| tf';ty |]
          (ty',tf',c') :: (ty,tf,c) :: xs
        let ((c0,_)::cases') = List.ofArray cases
        
        let constrsAndTypes =
          c0.GetFields()
          |> Array.map (fun pi -> pi.PropertyType)
          |> mkCase
          |> fun (tf,mk) -> List.foldBack caseCata cases' [(tf,tf,mk)]
          |> Array.ofList

        let lty = typeof<L<Meta,Meta>>.GetGenericTypeDefinition()
        let rty = typeof<R<Meta,Meta>>.GetGenericTypeDefinition()

        let mappings i (uc,gts) =
          let (ty,tf,constr) = constrsAndTypes.[i]
          if i = cases.Length - 1 then
            (gts,uc,constr)
          else
            let mutable c = fun (vals : Meta []) -> U() :> Meta
            for ix in 0 .. i do
              let (_,tf0,_) = constrsAndTypes.[ix]
              let (ty0,_,_)= constrsAndTypes.[ix + 1]
              if ix = 0 then
                let lty' = lty.MakeGenericType [| tf0;ty0 |]
                c <- fun (vals : Meta []) ->
                  lty'.GetConstructor([|tf0|]).Invoke [| constr vals |] :?> Meta
              else
                let rty' = rty.MakeGenericType [| tf0;ty0 |]
                c  <- c |> fun c' (vals : Meta[]) ->
                  rty'.GetConstructor([|ty0|]).Invoke [| c' vals |] :?> Meta
            (gts,uc,c)

        UC(cases |> Array.mapi mappings)

      override this.Prim(i,ty) =
        let kty = typeof<K<obj>>.GetGenericTypeDefinition().MakeGenericType([|ty|]).GetConstructor([|ty|])
        Prim (fun o -> kty.Invoke([|o|]) :?> Meta)

    let repType<'t> = Reflection.foldType<'t,_> (RepTypeAlg<'t>())

    (*
    type CalcTypeAlg<'t>() =
      inherit Reflection.ValAlg<'t,Meta>()

      override this.Id(i,t) = Id<'t>(t) :> _

      override this.Case(i,case,tys') =
        let (Some ucs,t') = case.DeclaringType |> repType
        let ix = ucs |> Array.findIndex (fun uc -> uc = case)
        let sumType = typeof<SumConstr<Meta,Meta>>.GetGenericTypeDefinition()
        let v = sumType.
                                  
        let ty =
          match tys' |> List.ofArray with
          | ty::tys -> List.foldBack (fun ty s -> sumType.MakeGenericType [|ty;s|]) tys ty
          | [] -> typeof<U>
        extend i ty
        ty

      override this.Prim(i,obj) =
        let kTy = typeof<K<obj>>.GetGenericTypeDefinition()
        let ty = kTy.MakeGenericType [|obj.GetType()|]
        extend i ty
        ty
    *)
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
(*
    type Meta with
      member o.Everywhere<'t>(f : int -> int) = (failwith "" : 't)
        // member o.Everywhere<'t>(f : int -> int) = 
        //     let t = o.GetType()
        //     let m = t.GetMethod("Everywhere", [|f.GetType()|])
        //     if m.ContainsGenericParameters then
        //         m.MakeGenericMethod([|typeof<'t>|]).Invoke(o,[|f|]) :?> 't
        //     else
        //         m.Invoke(o,[|f|]) :?> 't
        // (System.Exception("") |> raise) : 't

    type L<'a,'b when 'a :> Meta and 'b :> Meta> with
        member o.Everywhere(f : int -> int) =
          L<'a,'b>(o.Elem.Everywhere<'a>(f))

    type R<'a,'b when 'a :> Meta and 'b :> Meta> with
        member o.Everywhere(f : int -> int) = R<'a,'b>(o.Elem.Everywhere<'b>(f))

    type K<'t> with
        static member Everywhere(f : int -> int) = K(f o.Elem)
//        static member Everywhere(o : K<'v>, f : int -> int) = o

    type U with
        static member Everywhere(o : U, f : int -> int) = o
 
    type Id<'t> with
        static member Everywhere(o : Id<'t>, f : int -> int) =
            let g = Generic<'t>()
            Id<'t>(g.To(o.Elem).Everywhere<Meta>(f) |> g.From)

    type Prod<'a,'b when 'a :> Meta and 'b :> Meta> with
        static member Everywhere(o : Prod<'a,'b>, f : int -> int) =
            Prod<'a,'b>((o.E1.Everywhere<'a>(f),o.E2.Everywhere<'b>(f)))    
*)

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
          x.Matcher.Invoke(o,[||]) :?> bool
          
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

  open Reflection

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

  type K<'v,'r when 'v :> obj and 'r :> Meta>(elem : 'v, r : Meta) =
    inherit K<'v>(elem)
    member this.Rep with get() = r

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

  let (|K2|_|) (o : Meta) =
    try
      let t = o.GetType().GetGenericTypeDefinition().MakeGenericType([|typeof<obj>;typeof<Meta>|])
      let t' = typeof<K<obj,Meta>>
      if t.IsSubclassOf t' || t = t' then
        (o.GetType().GetProperty("Elem").GetValue(o),
         o.GetType().GetProperty("Rep").GetValue(o) :?> Meta) |> Some
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


  let rec unpack r =
    match r with
      | PROD (p1,p2) -> p1 :: unpack p2
      | U -> []
      | _ -> sprintf "The representation %A is not a Product" r |> failwith

  type GTree<'t> =
    | Prim of Type*(obj -> Meta)
    | Self of Type*('t -> Meta)
    | UC of Type*(((GTree<'t> [])*UnionCaseInfo*(obj -> Meta[] -> Meta)) [])
    with
      member o.RepType with get() =
        match o with
        | Prim (t,_) -> t
        | Self (t,_) -> t
        | UC (t,_) -> t 

  [<AbstractClass>]
  type ValAlg<'t,'s>() =
    abstract Id : int*Type*('t -> Meta)*'t -> 's
    abstract Case : int*Type*Reflection.UnionCaseInfo*(obj -> Meta[] -> Meta)*obj*('s[]) -> 's
    abstract Prim : int*Type*(obj -> Meta)*obj -> 's

  let foldVal<'t,'s> (t' : GTree<'t>) (alg : ValAlg<'t,'s>) (x : 't) =
    let count = ref 0
    let inc() = count := !count + 1;!count
    let rec fold' (t : GTree<'t>) (v : obj) =
      let i = inc()
      match t with
      | Prim (t,c) -> alg.Prim(i,t,c,v)
      | Self (t,c) -> alg.Id(i,t,c,v :?> 't)
      | UC (t,ucs) ->
        let ty = v.GetType()
        let (gts,uc,c) = ucs |> Array.find (fun (_,uc,_) -> uc.Matches v)
        let prev = Reflection.FSharpValue.GetUnionFields(v,ty)
                   |> (fun (_,objs) -> Array.zip gts objs)
                   |> Array.map (fun (gt,o) -> fold' gt o)
        alg.Case(i,t,uc,c,v,prev)
    fold' t' x
          
  type RepTypeAlg<'t>() =
    inherit Reflection.TyAlg<'t,GTree<'t>>()

    override this.Id(i,ty) = Self(typeof<Id<'t>>,fun v -> Id<'t>(v) :> _)

    override this.Case(i,cases) =

      let pTy = typeof<Prod<Meta,Meta>>.GetGenericTypeDefinition()
      // Function to pack the constituents of a type constructor into a
      // sequential application of the Prod constructor
      let mkCase tys =
        // tf corresponds to the type of the representation
        // constrs corresponds to the constructors that create the type representation
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
      let caseCata ((ty,tf,c)::xs) (uc : UnionCaseInfo,vals : GTree<'t> []) =
        let (tf',c') =
          vals
          |> Array.map (fun pi -> pi.RepType)
          |> mkCase
        
        let ty' = sTy.MakeGenericType [| tf';ty |]
        (ty',tf',c') :: (ty,tf,c) :: xs
      let ((c0,t0)::cases') = List.ofArray cases |> List.rev

      let constrsAndTypes =
        t0 
        |> Array.map (fun t -> t.RepType)
        |> mkCase
        |> fun (tf,mk) -> List.fold caseCata [(tf,tf,mk)] cases'
        |> Array.ofList

      let lty = typeof<L<Meta,Meta>>.GetGenericTypeDefinition()
      let rty = typeof<R<Meta,Meta>>.GetGenericTypeDefinition()
      let kTy2 = typeof<K<obj,Meta>>.GetGenericTypeDefinition()
      let (oTy,_) = cases.[0]

      let mkK2 rTy c' =
        let kty2 = kTy2.MakeGenericType [| oTy.DeclaringType;rTy |]
        let ckty2 = kty2.GetConstructor [| oTy.DeclaringType;rTy |]
        fun o ms ->
          ckty2.Invoke [| o; c' ms |] :?> Meta

      let mappings i (uc,gts) =
        let (ty,tf,constr) = constrsAndTypes.[i]
        if i = cases.Length - 1 then
          (gts,uc,mkK2 tf constr)
        else
          let mutable c = fun (vals : Meta []) -> U() :> Meta
          let mutable rTy = null
          for ix in 0 .. i do
            let (_,tf0,_) = constrsAndTypes.[ix]
            let (ty0,_,_)= constrsAndTypes.[ix + 1]
            if ix = 0 then
              let lty' = lty.MakeGenericType [| tf0;ty0 |]
              rTy <- lty'
              c <- fun (vals : Meta []) ->
                lty'.GetConstructor([|tf0|]).Invoke [| constr vals |] :?> Meta
            else
              let rty' = rty.MakeGenericType [| tf0;ty0 |]
              c  <- c |> fun c' (vals : Meta[]) ->
                rty'.GetConstructor([|ty0|]).Invoke [| c' vals |] :?> Meta
          (gts,uc,mkK2 rTy c)

      let ty = kTy2.MakeGenericType [|
        oTy.DeclaringType
        constrsAndTypes.[0] |> fun (ty,_,_) -> ty |]
      
      UC(ty,cases |> Array.mapi mappings)

    override this.Prim(i,ty) =
      let kty = typeof<K<obj>>.GetGenericTypeDefinition().MakeGenericType([|ty|])
      let ckty = kty.GetConstructor([|ty|])
      Prim (kty,fun o -> ckty.Invoke([|o|]) :?> Meta)

  let repType<'t> = Reflection.foldType<'t,_> (RepTypeAlg<'t>())

  type RepValAlg<'t>() =
    inherit ValAlg<'t,Meta>()
    override this.Id(i,ty,cs,o) = cs o
    override this.Case(i,ty,uc,cs,o,objs) = cs o objs
    override this.Prim(i,ty,cs,o) = cs o


  let toRep<'t> =
    let gt = repType<'t>
    foldVal<'t,Meta> gt (RepValAlg())

  [<AbstractClass>]
  type RepAlg<'t,'s>() =
    abstract Prim : int*Type*(obj -> Meta)*obj -> 's
    abstract Self : int*Type*('t -> Meta)*'t -> 's
    abstract Uc : int*Type*UnionCaseInfo*(obj -> Meta[] -> Meta)*'s[] -> 's

  let foldRep<'t,'s> gt' (alg : RepAlg<'t,'s>) rep' =
    let count = ref 0
    let inc() = count := !count + 1;!count
    let rec fold' (gt,rep) =
      let i = inc()
      match (gt,rep) with
      | (Prim (t,c),K v) -> alg.Prim(i,t,c,v)
      | (Self (t,c),ID v) -> alg.Self(i,t,c,v :?> 't)
      | (UC (ty,ucs),_)
      | (UC (ty,ucs),_) ->
        let (rep',(gts,uc,cs)) =
          let rec go (s : Meta*((GTree<'t> [])*UnionCaseInfo*(obj -> Meta[] -> Meta))) xs' =
            match (s,xs') with
              | (R v,_),x::xs -> go (v,x) xs
              | (L v,uc),_ 
              | (R v,uc),_ -> (v,uc)
              | (K2 (_,r),uc),_ -> go (r,uc) xs'
              | _ -> s
          let (u::ucs') = ucs |> List.ofArray
          go (rep,u) ucs'
        printf "Zippping \n%A \nand %A" (unpack rep') gts
        let res =
          unpack rep'
          |> Array.ofList
          |> Array.zip gts
          |> Array.map fold'
        alg.Uc(i,ty,uc,cs,res)
    fold' (gt',rep')

  type ValRepAlg<'t>() =
    inherit RepAlg<'t,obj>()

    override this.Uc(i,ty,uci,cs,args) =
      uci.Constructor.Invoke(null,args)

    override this.Prim(i,ty,cs,v) = v

    override this.Self(i,ty,cs,v) = v :> _

  let fromRep<'t> rep =
    let gt = repType<'t>
    foldRep gt (ValRepAlg<'t>()) rep :?> 't

  type Generic<'t>() =
    class
      let gt = repType<'t>
      member this.To(m : 't) =
        foldVal<'t,Meta> gt (RepValAlg()) m

      member this.From(rep : Meta) =
        foldRep gt (ValRepAlg<'t>()) rep :?> 't

    end

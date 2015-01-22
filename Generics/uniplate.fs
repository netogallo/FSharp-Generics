namespace Generics

open System
open Microsoft.FSharp.Reflection

module Uniplate =
    let a = id

module Reflection =

    [<CustomComparison>]
    type TypeConstructor<'t> = {

        Info : UnionCaseInfo
        Matcher : 't -> bool
        Invoke : array<obj> -> 't
        Elems : 't -> (obj*System.Type) [] option
        Params : System.Type []
        }
        with 
            interface IComparable with
                override o.CompareTo(o' : obj) = 
                    match o' with
                        | :? TypeConstructor<'t> as o'' -> 
                            compare (o.Info.Name,o.Info.Tag) (o''.Info.Name,o''.Info.Tag)
                        | _ -> 1

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
            Params = [||]    
        }


module Rep =

    type Microsoft.FSharp.Reflection.UnionCaseInfo with
        member x.Constructor with get() = x.DeclaringType.GetMethod(sprintf "New%s" x.Name)

    [<AbstractClass>]
    type Meta() =
      class
      end

    [<AbstractClass>]
    type Constr<'t>() =
      class
        inherit Meta()
      end
    
    type Meta with
        member o.From<'t>() = obj() :?> 't
        static member To<'t>(a : obj) = a :?> Constr<'t> 
      
    type Constr<'t> with
        member o.Everywhere<'a when 'a :> Meta>(a : 'a, f : int -> int) = obj() :?> 'a

    [<AbstractClass>]
    type SumConstr<'a,'b when 'a :> Meta and 'b :> Meta>() =
        class
            inherit Constr<Choice<'a,'b>>()
            // abstract Elem : Choice<'a,'b> with get
        end

    type L<'a,'b when 'a :> Meta and 'b :> Meta>(elem : 'a) =
      class
        inherit SumConstr<'a,'b>()
        member o.Elem with get() = elem
      end

    type L<'a,'b when 'a :> Meta and 'b :> Meta> with
        member o.Everywhere(f) = L<'a,'b>(o.Everywhere<'a>(o.Elem,f))

    // type L2<'c,'t>(elem : 't) = class end

    type R<'a,'b when 'a :> Meta and 'b :> Meta>(elem : 'b) =
      class
        inherit SumConstr<'a,'b>()
        member o.Elem with get() = elem
      end
    
    type R<'a,'b when 'a :> Meta and 'b :> Meta> with
        member o.Everywhere(f) = R<'a,'b>(o.Everywhere<'b>(o.Elem,f))

    type Prod<'a,'b when 'a :> Meta and 'b :> Meta>(elem : 'a*'b) =
      class
        inherit Constr<'a*'b>()
        member o.Elem with get() = elem
      end
    
    type Prod<'a,'b> with
        member o.Everywhere(f) =
            let (a,b) = o.Elem
            Prod(o.Everywhere<'a>(a,f),o.Everywhere<'b>(b,f))


    type Id<'t>(elem : 't) =
      class
        // inherit Constr<'t>()
        member o.Elem with get() = elem
      end
      
    type Id<'t> with
        member o.Everywhere(f) = 
            let c = Meta.To o.Elem
            Id(c.Everywhere(c,f).From())
    
    type K<'v>(elem : 'v) =
      class
        member o.Elem with get() = elem
      end

    type K<'v> with
        member o.Everywhere(f) = K(f o.Elem)
    
    type U() =
      class
        //inherit Constr<'t>()
      end

    type U with
        member o.Everywhere(f) = U() 
    
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
    *)

    [<AbstractClass>]
    type Everywhere<'c,'t, 'u when 'c :> Constr<'t> and 't :> Constr<'u>>() =
    
      member o.Everywhere(meta:L<'t,'u>, r:obj,f:int -> int) =
        L(o.Everywhere(meta.Elem,f)) :> Constr<'t>
   
   (* 
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
    *)
      abstract Everywhere : 't*(int -> int) -> 't
      
      // abstract To : Constr<'t> -> 't

    type AList<'t> = Cons of 't*AList<'t> | Nil
    
    type AListP<'c> =
      {
        list : AList<int>
        meta : 'c
       }        

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
    
namespace Generics

open System
open System.Reflection

module Selector =
  open Rep;

  let Sg = typeof<Rep.SumConstr<obj,Rep.Meta,Rep.Meta>>.GetGenericTypeDefinition()
  let Prodg = typeof<Rep.Prod<Rep.Meta,Rep.Meta>>.GetGenericTypeDefinition()
  let Idg = typeof<Rep.Id<obj>>.GetGenericTypeDefinition()
  let Kg = typeof<Rep.K<obj>>.GetGenericTypeDefinition()


  let rec (<~>) (t1 : Type) (t2 : Type) =
    match (t1,t2) with
    | (SUMTY (t,(MTY as m1),(MTY as m2)), SUMTY (t',(MTY as m1'),(MTY as m2'))) when t = t' -> 1 + (m1 <~> m1') + (m2 <~> m2')
    | (PRODTY ((MTY as m1), (MTY as m2)), PRODTY ((MTY as m1'),(MTY as m2'))) -> 1 + (m1 <~> m1') + (m2 <~> m2')
    | _ when t1 = t2 -> 1
    | _ -> 0
                  
  let (>!) x' y' = 
      let mkTup (t1,t2) =
          typeof<obj*obj>.GetGenericTypeDefinition().MakeGenericType([|t1;t2|])
      let rec op = function
          | (x,t) when t = typeof<Rep.Meta> -> x :> Rep.Meta
          | (Rep.U as x, t : Type) -> x
          | (x,t : Type) ->
              let genericsOrFail (t : Type) =
                  if t.IsGenericType then
                      t.GenericTypeArguments
                  else
                      sprintf "Failed to convert %A to type %s" x t.FullName |> failwith
              let typeArgs = genericsOrFail t
              match x with
              | Rep.L m ->
                let e = op(m,typeArgs.[1])
                let cTy = typeof<Choice<obj,obj>>.GetGenericTypeDefinition().MakeGenericType [| typeArgs.[1];typeArgs.[2] |]
                let choice x = cTy.GetMethod("NewChoice1Of2").Invoke(null,[| x |])
                x.GenericInit typeArgs [|choice e, cTy |]
              | Rep.R m ->
                let e = op(m,typeArgs.[2])
                let cTy = typeof<Choice<obj,obj>>.GetGenericTypeDefinition().MakeGenericType [| typeArgs.[1];typeArgs.[2] |]
                let choice x = cTy.GetMethod("NewChoice2Of2").Invoke(null,[| x |])
                x.GenericInit typeArgs [|choice e,cTy |]
              | Rep.PROD (a,b) ->
                  x.GenericInit typeArgs [|
                    op(a,typeArgs.[0]) :> obj, typeArgs.[0]
                    op(b,typeArgs.[1]) :> obj, typeArgs.[1]
                  |]
              | Rep.ID i ->
                  x.GenericInit typeArgs [| i,typeArgs.[0] |]
              | Rep.K v ->
                  x.GenericInit typeArgs [| v,typeArgs.[0] |]
      
      op (x',y')

  let basePrefix = "__BASE"
  let mkBaseName n = sprintf "%s%s" n basePrefix

  type Selector(obj : obj, ``method`` : string, args : Type []) =    

    let baseMethodFilter (m : MethodInfo) =
      let args' = m.GetParameters() 
                |> Array.map (fun arg -> arg.ParameterType)
                |> Array.toList

      match args' with
      | x::xs -> m.Name = ``method``
                && x.IsSubclassOf typeof<Meta>
                && xs = Array.toList args
      | _ -> false

    let methods = obj.GetType().GetMethods(
                    BindingFlags.FlattenHierarchy 
                    ||| BindingFlags.Instance 
                    ||| BindingFlags.Public) 
                  |> Array.filter baseMethodFilter

    let uMethods = methods |> Array.filter (fun m -> match m.GetParameters().[0].ParameterType with
                                                      | UTY -> true
                                                      | _ -> false)

    let sMethods = methods |> Array.filter (fun m -> match m.GetParameters().[0].ParameterType with
                                                      | SUMTY _ -> true
                                                      | _ -> false)

    let pMethods = methods |> Array.filter (fun m -> match m.GetParameters().[0].ParameterType with
                                                      | PRODTY _ -> true
                                                      | _ -> false)

    let iMethods =  methods |> Array.filter (fun m -> match m.GetParameters().[0].ParameterType with
                                                      | IDTY _ -> true
                                                      | _ -> false)

    let kMethods =  methods |> Array.filter (fun m -> match m.GetParameters().[0].ParameterType with
                                                      | KTY _ -> true
                                                      | _ -> false)

    let instantiator types (m : MethodInfo) =
      if m.IsGenericMethod then
        m.MakeGenericMethod types
      else
        m

    member x.SelectMethod(c : Rep.Meta) =
      let cty = c.GetType()
      let mCmp tys (mi : MethodInfo) = 
        if mi.IsGenericMethod then
          cty <~> (mi.MakeGenericMethod(tys).GetParameters().[0].ParameterType)
        else
          1 + (cty <~> (mi.GetParameters().[0].ParameterType))

      let inst tys (mi : MethodInfo) = 
        if mi.IsGenericMethod then mi.MakeGenericMethod(tys) else mi

      match cty with
      | SUMTY (t,_,_) -> sMethods |> Array.maxBy (mCmp [|t|]) |> inst [|t|]
      | PRODTY _ -> pMethods |> Array.maxBy (mCmp [||])
      | KTY t -> kMethods |> Array.maxBy (mCmp [|t|]) |> inst [|t|]
      | IDTY _ -> iMethods |> Array.maxBy (mCmp [||])
      | UTY -> uMethods |> Array.maxBy (mCmp [||])
      | _ -> failwith "The type representation %A is not recoginezed" cty

    member x.SelectInvoke(c : Rep.Meta, args : obj []) =
        let m = x.SelectMethod(c)
        let arg = m.GetParameters().[0].ParameterType
        let allArgs = Array.append [|c >! arg :> obj |] args
        try
            m.Invoke(obj, allArgs)
        with
            | :? System.Reflection.TargetParameterCountException as e -> sprintf "Could not invoke %A with %A" m args |> failwith

  module Monofold =
    
    type Inh<'x>(elem : 'x) = 
      class 
        member x.Elem with get() = elem
      end
    
      // M,U
    
    type Inh<'x,'y>(x : 'x, inh : 'x -> 'y) = 
      class
      inherit Inh<'y>(inh x)
      //base.Elem :> 'y
      end

    type Inh<'x,'y> with
      static member Inh<'a> a = Inh<'a,'a>(a,id)
    
    type Meta with
      static member Inh<'a when 'a :> Meta> x = Inh<'a,Meta>(x,fun x -> x :> Meta)
    
    [<AbstractClass>]
    type Monofold<'i,'m,'s,'p,'id,'k,'u>() as this =
        
      let selector = Selector(this,"Monofold",[||])

      abstract Monofold : Meta -> Inh<'m>
      default __.Monofold (m : Meta) = selector.SelectInvoke(m,[||]) :?> Inh<'m>

      abstract Monofold<'x> : SumConstr<'x,Meta,Meta> -> Inh<'m,'p>
      
      abstract Monofold : Prod<Meta,Meta> -> Inh<'m,'p>

      abstract Monofold : Id<'i> -> Inh<'m,'id>

      abstract Monofold<'x> : K<'x> -> Inh<'m,'k>
      
      abstract Monofold : U -> Inh<'s,'u>

    [<AbstractClass>]
    type Monofold<'i,'t>() as this =

      //inherit Monofold<'i,'t,'t,'t,'t,'t,'t>()
      let selector = Selector(this,"Monofold",[||])
      abstract Monofold : Meta -> 't
      //default __.Monofold (m : Meta) = (base.Monofold m).Elem
      default __.Monofold (m : Meta) = selector.SelectInvoke(m,[||]) :?> 't

      abstract Monofold<'x> : SumConstr<'x,Meta,Meta> -> 't

(*      
      override self.Monofold<'x>(v : SumConstr<'x,Meta,Meta>) =
        Inh<'t,'t>.Inh(self.Monofold<'x>(v) : 't)
*)
      abstract Monofold : Prod<Meta,Meta> -> 't

      abstract Monofold : Id<'i> -> 't

      abstract Monofold<'x> : K<'x> -> 't

      abstract Monofold : U -> 't
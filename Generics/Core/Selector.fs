﻿namespace Generics

open System
open System.Reflection

module Selector =

    let Sg = typeof<Rep.SumConstr<Rep.Meta,Rep.Meta>>.GetGenericTypeDefinition()
    let Prodg = typeof<Rep.Prod<Rep.Meta,Rep.Meta>>.GetGenericTypeDefinition()
    let Idg = typeof<Rep.Id<obj>>.GetGenericTypeDefinition()
    let Kg = typeof<Rep.K<obj>>.GetGenericTypeDefinition()


    let (?=) m1' m2' =
        let rec op =
            function 
                | (m1 : Type, m2 : Type) when m2.IsSubclassOf m1 -> true
                | (m1, m2) when m1.IsGenericType && m2.IsGenericType && m1.GetGenericTypeDefinition() = m2.GetGenericTypeDefinition() ->
                    let args1,args2 = m1.GetGenericArguments(), m2.GetGenericArguments()
                    if args1 = args2 then
                        true
                    else
                        Array.zip args1 args2 |> Array.forall op
                | (m1,m2) -> m1 = m2


        op (m1',m2')

    let (>~) m1' m2' =
        let rec op =
            function 
                | (m1 : Type, m2 : Type) when m1.IsSubclassOf m2 -> true
                | (m1,m2) when m1.IsGenericType && m2.IsGenericType && m1.GetGenericTypeDefinition() = m2.GetGenericTypeDefinition() ->
                    let args1,args2 = m1.GetGenericArguments(), m2.GetGenericArguments()
                    if args1 = args2 then
                      true
                    else
                      Array.zip args1 args2 |> Array.forall op
                | (m1,m2) -> m1 = m2
        op (m1',m2')
                    
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
                  let e = op(m,typeArgs.[0])
                  let cTy = typeof<Choice<obj,obj>>.GetGenericTypeDefinition().MakeGenericType(typeArgs)
                  let choice x = cTy.GetMethod("NewChoice1Of2").Invoke(null,[| x |])
                  x.GenericInit typeArgs [|choice e, cTy |]
                | Rep.R m ->
                  let e = op(m,typeArgs.[1])
                  let cTy = typeof<Choice<obj,obj>>.GetGenericTypeDefinition().MakeGenericType(typeArgs)
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

    type Selector() as this =    

        member x.SelectMethod(m : string, c : Rep.Meta, args : obj []) =

            let mt = c.GetType()

            let methodFinder name (constr : Rep.Meta) =
                let gt = constr.GetType()
                let select = function 
                    | (m : MethodInfo) when m.GetParameters().Length = 0 -> false
                    | m when m.GetParameters().[0].ParameterType.IsSubclassOf typeof<Rep.Meta> -> m.GetParameters().[0].ParameterType ?= mt
                    | _ -> false
                x.GetType().GetMethods(BindingFlags.FlattenHierarchy ||| BindingFlags.Instance ||| BindingFlags.Public) |> Array.filter (fun m -> select m)
            
            let darwin (m1 : MethodInfo) (m2 : MethodInfo) = 
                if m1.GetParameters().[0].ParameterType >~ m2.GetParameters().[0].ParameterType then
                    m1
                else
                    m2

            let methods = methodFinder m c
            if methods.Length > 0 then
                methods |> Array.fold darwin (methods.[0])
            else
                failwith <| sprintf "Method with name '%s' could not be found for type %A." m c

        member x.SelectInvoke(m : string, c : Rep.Meta, args : obj []) =
            let m = x.SelectMethod(m, c, args)
            let arg = m.GetParameters().[0].ParameterType
            let allArgs = Array.append [|c >! arg :> obj |] args
            try
                m.Invoke(x, allArgs)
            with
                | :? System.Reflection.TargetParameterCountException as e -> sprintf "Could not invoke %A with %A" m args |> failwith
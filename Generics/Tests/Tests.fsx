#r @"../Core/bin/Debug/Generics.dll"
#r @"../Provider/bin/Debug/Provider.dll"

open Generics.Rep
open Microsoft.FSharp.Core.CompilerServices

type Emp = Full of string*int | Part of string*int*int
type List<'t> = Cons of 't*List<'t> | Nel | Tip of 't

let g = Generic<List<Emp>>()

type CollectBase = Generics.Provided.Generic<"Collect",0>

type Collect<'t>() =
  inherit CollectBase(fun m -> ([] :'t list) :> obj)

  member x.Collect(m : Meta) =
    base.Collect m :?> 't list

  member x.Collect<'x>(c : SumConstr<'x,Meta,Meta>) =
    match c with
    | L m -> x.Collect m
    | R m -> x.Collect m

  member x.Collect(c : Prod<Meta,Meta>) =
    List.concat<'t> [x.Collect c.E1;x.Collect c.E2]
    // x.Collect c.E1

  member x.Collect(i : Id<'t>) =
    [i.Elem]

type InstantiateBase = Generics.Provided.Generic<"Instantiate",0>

type Instantiate<'t>(values' : 't list) =
  inherit InstantiateBase(fun m -> m :> obj)
  let mutable values = values'

  let pop () = match values with
                | x::xs -> values <- xs;Some x
                | [] -> None

  member x.Instantiate(m : Meta) = base.Instantiate m :?> Meta

  member x.Instantiate(s : SumConstr<'t,Meta,Meta>) =
    match s with
    | L m -> SumConstr<'t,Meta,Meta>(x.Instantiate(m) |> Choice1Of2)
    | R m -> SumConstr<'t,Meta,Meta>(x.Instantiate(m) |> Choice2Of2)

  member x.Instantiate(s : SumConstr<unit,Meta,Meta>) =
    match s with
    | L m -> SumConstr<'t,Meta,Meta>(x.Instantiate(m) |> Choice1Of2)
    | R m -> SumConstr<'t,Meta,Meta>(x.Instantiate(m) |> Choice2Of2)

  member x.Instantiate(i : Id<'t>) =
    match pop () with
    | Some x -> Id x
    | None -> i

type UniplateBase = Generics.Provided.Generic<"Uniplate",0>

type Uniplate<'t>() =
  inherit UniplateBase(fun m -> ([],fun _ -> m) :> obj)

  member x.Uniplate(s : SumConstr<'t,Meta,Meta>) =
    (Collect().Collect s,fun vs -> Instantiate(vs).Instantiate s)

let up = Uniplate<List<Emp>>()

let l1 = Cons(Full("pepe",2),Cons(Part("victor",8,4),Nel))

l1 |> g.To |> up.Uniplate

Prod<Meta,Meta>(U(),U()) |> ignore

type EverywhereBase = Generics.Provided.Generic<"Everywhere",0>

type Everywhere<'t,'v>(f : 'v -> 'v) =
    inherit EverywhereBase(fun m -> m :> obj)
    let g = Generic<'t>()

    member x.Everywhere(c : Meta) =
      base.Everywhere(c) :?> Meta

    member x.Everywhere<'t>(c : SumConstr<'t,Meta,Meta>) =
        printf "%A\n" c
        match c with
        | L m -> SumConstr<'t,Meta,Meta>(x.Everywhere(m) |> Choice1Of2)
        | R m -> SumConstr<'t,Meta,Meta>(x.Everywhere(m) |> Choice2Of2)

    member x.Everywhere(c : Prod<Meta,Meta>) =
        printf "%A\n" c
        let v1 = x.Everywhere(c.E1)
        let v2 = x.Everywhere(c.E2)
        Prod<Meta,Meta>((v1,v2))

    member x.Everywhere(c : K<'v>) =
        printf "A 't %A\n" c.Elem
        K<'v>(f c.Elem)

    member x.Everywhere(c : Id<'t>) =
        let g = Generic<'t>()
        Id<'t>(x.Everywhere(g.To c.Elem) |> g.From)

let everywhere<'t,'v> (f : 'v -> 'v) (a : 't) =
    let g = Generic<'t>()
    let e = Everywhere<'t,'v>(f)
    g.To a |> e.Everywhere :?> Meta |> g.From

type Emp = Full of string*int | Part of string*int*int
type List<'t> = Cons of 't*List<'t> | Nel

let l1 = Cons(Full("pepe",2),Cons(Part("victor",8,4),Nel))

everywhere (fun i -> i + i) l1
everywhere (fun (s : string) -> s.ToUpper()) l1

everywhere (fun i -> i + i) l1
|> everywhere (fun (s : string) -> s.ToUpper())

#r @"../Core/bin/Debug/Generics.dll"
open Generics.Rep
open Generics.Reflection


let t = repType<List<Emp>>

let uc = Reflection.FSharpType.GetUnionCases typeof<List<Emp>>;;

let u = uc.[0]

u.GetFields() |> Seq.cast<System.Type> |> Array.ofSeq

let l1 = Cons(Full("pepe",2),Cons(Part("victor",8,4),Nel))

let r = toRep<List<Emp>>(l1)

fromRep<List<Emp>> r

match r with
  | L(v) -> v

u.Matcher.Invoke((Nel : List<Emp>),[||])

let a = CalcTypeAlg<List<Emp>>()

foldType a l1

type X() = class end

type A() =
  class
    member x.X<'t when 't :> X>(a :'t) = sprintf "A: %A" a
  end

type B() =
  class
    inherit A()
    member x.X<'t>(a : 't) = sprintf "B: %A" a
  end

B().X<X>(X())

let [| x  |] =  typeof<A>.GetMethods() |> Array.filter (fun m -> m.Name = "X")

let [| c |] = x.GetGenericArguments() |> Array.map (fun ti -> ti.GetGenericParameterConstraints())

x.GetParameters().[0].ParameterType.GetGenericTypeDefinition()

x.IsGenericMethod

x.MakeGenericMethod([| typeof<int> |]).Invoke(A(),[| 5 |])

let (x : System.Reflection.PropertyInfo) = failwith ""

x.

type B() =
  inherit A()


[| B() |] :> obj :?> (A[])

[| B() :> A |] :> obj :?> (A[])
kk

let mutable count = fun () -> printfn "Hay"

for ix in 0 .. 0 do
  printfn "haja"

for ix in 1 .. 5 do
  count <- count |> fun count' () -> count' ();printfn "Hay"

type T = A of int | B of string

let g = Generic<T>()

A 5 |> g.To

let (|SUM|_|)<'t,'a,'b when 'a :> Meta and 'b :> Meta> (m : Meta) =
  if m.GetType() = typeof<SumConstr<'t,'a,'b>> then
    let s = m :?> SumConstr<'t,'a,'b>
    match s.Elem with
    | Choice1Of2 s' -> Choice1Of2 ((None : 't option),s')
    | Choice2Of2 s' -> Choice2Of2 ((None : 't option),s')
    |> Some
  else
    None

match A 5 |> g.To with
  | SUM (c : Choice<(T option)*Meta,(T option)*Meta>) -> ()

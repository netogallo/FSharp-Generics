#r @"../Core/bin/Debug/Generics.dll"
#r @"../Provider/bin/Debug/Provider.dll"

open Generics.Rep
open Microsoft.FSharp.Core.CompilerServices

Prod<Meta,Meta>(U(),U()) |> ignore

type EverywhereBase = Generics.Provided.Generic<"Everywhere",0>

type Everywhere<'t,'v>(f : 'v -> 'v) =
    inherit EverywhereBase(fun m -> m :> obj)
    let g = Generic<'t>()

    member x.Everywhere(c : Meta) =
      base.Everywhere(c) :?> Meta

    member x.Everywhere(c : L<Meta,Meta>) =
        printf "%A\n" c
        L<Meta,Meta>(x.Everywhere(c.Elem))

    member x.Everywhere(c : R<Meta,Meta>) =
        printf "%A\n" c
        R<Meta,Meta>(x.Everywhere(c.Elem))

    member x.Everywhere(c : Prod<Meta,Meta>) =
        printf "%A\n" c
        let v1 = x.Everywhere(c.E1)
        let v2 = x.Everywhere(c.E2)
        Prod<Meta,Meta>(v1,v2)

    member x.Everywhere(c : K<'v>) =
        printf "A 't %A\n" c.Elem
        K<'v>(f c.Elem)

    member x.Everywhere(c : Id<'t>) =
        let g = Generic<'t>()
        Id<'t>(x.Everywhere(g.To c.Elem) |> g.From)

let everywhere<'t,'v> (f : 'v -> 'v) (a : 't) =
    let g = Generic<'t>()
    let e = Everywhere<'t,'v>(f)
    g.To a |> e.Everywhere |> g.From

type Emp = Full of string*int | Part of string*int*int
type List<'t> = Cons of 't*List<'t> | Nel

let l1 = Cons(Full("pepe",2),Cons(Part("victor",8,4),Nel))

everywhere (fun e -> match e with
            | Full (n,v) -> Full ("juan",v - 1)
            | _ -> e) l1

everywhere (fun i -> i + i) l1
everywhere (fun (s : string) -> s.ToUpper()) l1

everywhere (fun i -> i + i) l1
|> everywhere (fun (s : string) -> s.ToUpper())

#r @"../Core/bin/Debug/Generics.dll"
open Generics.Rep
open Generics.Reflection

type Emp = Full of string*int | Part of string*int*int
type List<'t> = Cons of 't*List<'t> | Nel | Tip of 't

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

type A() =
  class
  end

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

type M private () =
  class
    static member Mk() = M()
  end

M.Mk()

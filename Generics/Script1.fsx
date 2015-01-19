type Kaiser = Toro of int | Rico of string*int

type List<'t> = Cons of 't*List<'t> | SemiCons of 't | Nil

type Microsoft.FSharp.Reflection.UnionCaseInfo with
    member x.Constructor with get() = 
        x.DeclaringType.GetMethods() 
        |> Array.find (fun mi -> mi.Name = sprintf "New%s" x.Name || mi.Name = sprintf "get_%s" x.Name)
    member x.Matcher with get() =
        x.DeclaringType.GetMethod(sprintf "get_Is%s" x.Name)

let constrs = Microsoft.FSharp.Reflection.FSharpType.GetUnionCases typeof<List<Kaiser>>

constrs.[0].DeclaringType.GetNestedType(constrs.[0].Name).GetMethods() |> Array.filter (fun mi -> mi.Name.Contains "get_Item")

constrs.[0].DeclaringType.GetMethods() |> Array.filter (fun mi -> mi.Name.Contains "Nil")

typeof<int>
//constrs.[0].Constructor.[0].DeclaringType.GetMethod("NewCons").GetParameters() // .MemberType

type TypeConstructor<'t> = {

        Matcher : 't -> bool
        Invoke : array<obj> -> 't
        Elems : 't -> (obj*System.Type) [] option
        Params : System.Type []
    }

open Microsoft.FSharp.Reflection

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
        Matcher = matcher
        Invoke = invoke
        Elems = elems
        Params = [||]    
    }

constrs.[2].DeclaringType.GetNestedTypes() |> Array.map (fun t -> t.Name) //.Constructor.Invoke(null,[||])
MakeTypeConstructor<List<Kaiser>>(constrs.[2]).Elems (SemiCons (Toro 5) : List<Kaiser>) //.Elems (Cons (Toro 6,Nil))

\DeclaringType.Module.GetTypes() |> Array.map (fun
 mi -> mi.Name)

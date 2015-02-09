type Comp = A of int | B of string | C of bool

type List<'t> = Cons of 't*List<'t> | SemiCons of 't | Nil

let g = Generic<List<Comp>>()

g.To(Cons(A 4, Cons ((B "hello"), Cons((C true), Nil)))).Everywhere<Meta>(id)


type E() = class
    member x.Lele<'t>(a : 't) = ()
end

typeof<E>.Attributes

let f = E.Lele

f.ToString()

[<AbstractClass>]
type x() = class end

typeof<x>.GetConstructors()

open System.Reflection

TypeAttributes.Abstract ||| TypeAttributes.AnsiClass ||| TypeAttributes.AutoLayout

let code = """

        namespace Generics.Provided {
            public class T {

                public int elem(){return 8;}
                // public T(){}
                public abstract class P{
                    public abstract void call(int v);
                }

            }
        }
"""
let dll = System.IO.Path.GetTempFileName()
let csc = new Microsoft.CSharp.CSharpCodeProvider()
let args = System.CodeDom.Compiler.CompilerParameters()
args.OutputAssembly <- dll
args.CompilerOptions <- "/t:library"
let compiled = csc.CompileAssemblyFromSource(args, [| code |])
compiled.Errors
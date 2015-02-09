﻿namespace Generics

open System
open System.Reflection
open Microsoft.FSharp.Core.CompilerServices
open Microsoft.FSharp.Quotations
//open Samples.FSharp.ProvidedTypes
open Generics.Rep
open System.Globalization

[<assembly:TypeProviderAssembly>] 
do()

module Provider =
   
    let libAsm = @"C:\Users\N\Documents\Visual Studio 2013\FSharp-Generics\Generics\bin\Debug\Generics.dll"

    type GenType(t : Type, name : string) =
        inherit Type()

        member this.Invoker<'T> call (tys : Type []) args =
            try
                let ty = t.GetType()
                let m = 
                    if ty.GetMethod(call, tys) = null then
                        ty.GetMethod(call, BindingFlags.FlattenHierarchy ||| BindingFlags.NonPublic ||| BindingFlags.Instance)
                    else
                        ty.GetMethod(call, tys)
                m.Invoke(t,args) :?> 'T
            with
                | e -> System.IO.File.WriteAllText(@"C:\Users\N\Downloads\error.txt",sprintf "Err %A with %A %A %A" e call tys args)
                        |> failwith ""
        
        override this.Name with get() = name
        
        override this.HasElementTypeImpl() = this.Invoker "HasElementTypeImpl" [||] [||]
        override this.IsPrimitiveImpl() = this.Invoker "IsPrimitiveImpl" [||] [||]
        override this.IsPointerImpl() = this.Invoker "IsPointerImpl" [||] [||]
        override this.IsCOMObjectImpl() = this.Invoker "IsCOMObjectImpl" [||] [||]
        override this.IsByRefImpl() = this.Invoker "IsByRefImpl" [||] [||]
        override this.IsArrayImpl() = this.Invoker "IsArrayImpl" [||] [||]
        override this.GetAttributeFlagsImpl() = this.Invoker "GetAttributeFlagsImpl" [||] [||]
        override this.GetPropertyImpl(a,b,c,d,e,f) = this.Invoker "GetPropertyImpl" [|typeof<String>;typeof<BindingFlags>;typeof<Binder>;typeof<Type>;typeof<Type[]>;typeof<ParameterModifier[]>|] [|a;b;c;d;e;f|]
        override this.GetMethodImpl(a,b,c,d,e,f) = this.Invoker "GetMethodImpl" [|typeof<String>;typeof<BindingFlags>;typeof<Binder>;typeof<CallingConventions>;typeof<Type[]>;typeof<ParameterModifier[]>|] [|a;b;c;d;e;f|]
        override this.GetConstructorImpl(a,b,c,d,e) = this.Invoker "GetConstructorImpl" [|typeof<BindingFlags>;typeof<Binder>;typeof<CallingConventions>;typeof<Type[]>;typeof<ParameterModifier[]>|] [|a;b;c;d;e|]
        override this.GetMethods(a) = this.Invoker "GetMethods" [|typeof<BindingFlags>|] [|a|]
        override this.get_GUID() = this.Invoker "get_GUID" [||] [||]
        override this.InvokeMember(a,b,c,d,e,f,g,h) = this.Invoker "InvokeMember" [|typeof<String>;typeof<BindingFlags>;typeof<Binder>;typeof<Object>;typeof<Object[]>;typeof<ParameterModifier[]>;typeof<CultureInfo>;typeof<String[]>|] [|a;b;c;d;e;f;g;h|]
        override this.get_Module() = this.Invoker "get_Module" [||] [||]
        override this.get_Assembly() = this.Invoker "get_Assembly" [||] [||]
        override this.get_FullName() = this.Invoker "get_FullName" [||] [||]
        override this.get_Namespace() = this.Invoker "get_Namespace" [||] [||]
        override this.get_AssemblyQualifiedName() = this.Invoker "get_AssemblyQualifiedName" [||] [||]
        override this.get_BaseType() = this.Invoker "get_BaseType" [||] [||]
        override this.GetConstructors(a) = this.Invoker "GetConstructors" [|typeof<BindingFlags>|] [|a|]
        override this.GetField(a,b) = this.Invoker "GetField" [|typeof<String>;typeof<BindingFlags>|] [|a;b|]
        override this.GetFields(a) = this.Invoker "GetFields" [|typeof<BindingFlags>|] [|a|]
        override this.GetInterface(a,b) = this.Invoker "GetInterface" [|typeof<String>;typeof<Boolean>|] [|a;b|]
        override this.GetInterfaces() = this.Invoker "GetInterfaces" [||] [||]
        override this.GetEvent(a,b) = this.Invoker "GetEvent" [|typeof<String>;typeof<BindingFlags>|] [|a;b|]
        override this.GetEvents(a) = this.Invoker "GetEvents" [|typeof<BindingFlags>|] [|a|]
        override this.GetProperties(a) = this.Invoker "GetProperties" [|typeof<BindingFlags>|] [|a|]
        override this.GetNestedTypes(a) = this.Invoker "GetNestedTypes" [|typeof<BindingFlags>|] [|a|]
        override this.GetNestedType(a,b) = this.Invoker "GetNestedType" [|typeof<String>;typeof<BindingFlags>|] [|a;b|]
        override this.GetMembers(a) = this.Invoker "GetMembers" [|typeof<BindingFlags>|] [|a|]
        override this.GetElementType() = this.Invoker "GetElementType" [||] [||]
        override this.get_UnderlyingSystemType() = this.Invoker "get_UnderlyingSystemType" [||] [||]
        override this.GetCustomAttributes(a) = this.Invoker "GetCustomAttributes" [|typeof<Boolean>|] [|a|]
        override this.GetCustomAttributes(a,b) = this.Invoker "GetCustomAttributes" [|typeof<Type>;typeof<Boolean>|] [|a;b|]
        override this.IsDefined(a,b) = this.Invoker "IsDefined" [|typeof<Type>;typeof<Boolean>|] [|a;b|]
      
    type Extensible() = inherit obj()


    type Generic() = inherit obj()

    let ns = "Generics.Provided"

    let makeClass name = 
        let decl = sprintf """
        namespace %s {
        using System.Reflection;
        using System;
        using Generics;

            public class %s : Selector.Selector{

                public void methods(){

                    foreach(var m in this.GetType().GetMethods(BindingFlags.FlattenHierarchy | BindingFlags.Instance | BindingFlags.Public)){
                        Console.WriteLine(m.Name);
                    }
                }
            }
        }
        """ 
        decl ns name

    let private AssemblyStore = Collections.Generic.Dictionary<Assembly,byte[]>()

    let makeCompiledClass name =
        let code = makeClass name
        System.IO.File.WriteAllText(@"C:\Users\N\Downloads\source.c", code)
        let dll = System.IO.Path.GetTempFileName()
        let csc = new Microsoft.CSharp.CSharpCodeProvider()
        let args = System.CodeDom.Compiler.CompilerParameters()
        args.OutputAssembly <- dll
        args.CompilerOptions <- "/t:library"
        args.CompilerOptions <- sprintf "/r:\"%s\"" libAsm
        let compiled = csc.CompileAssemblyFromSource(args, [| code |])
        let errFile = @"C:\Users\N\Downloads\compileErrs.c"
        let errs = seq{
            for e in compiled.Errors do
            yield e
        }
        System.IO.File.WriteAllText(errFile, errs |> Seq.fold (fun s e -> sprintf "%s%s : %i" s e.ErrorText e.Line + System.Environment.NewLine) "" )

        let asm = compiled.CompiledAssembly
        AssemblyStore.Add(asm,System.IO.File.ReadAllBytes dll)
        (asm.GetType(sprintf "%s.%s" ns name), asm)

    [<TypeProvider>]
    type GenericProvider() =
        let invalidation = new Event<EventHandler, EventArgs>()
        let mutable ty = None
        interface IProvidedNamespace with
            member this.ResolveTypeName(typeName) = typeof<Generic>
            member this.NamespaceName with get() = ns
            member this.GetNestedNamespaces() = [| |]
            member this.GetTypes() = [| typeof<Generic> |]
        interface ITypeProvider with
            member this.GetNamespaces() = [| this |]
            member this.ApplyStaticArguments(noArgs,withArgs,b) = 
                match ty with
                | Some ty' -> GenType(ty',(withArgs.[withArgs.Length - 1])) :> _
                | None ->
                    let (t,_) = makeCompiledClass <| withArgs.[withArgs.Length - 1]
                    ty <- Some t 
                    t
            member this.GetStaticParameters(typeWithoutArguments) = 
                let p = {new ParameterInfo() with
                            override x.Name with get() = "A1"
                            override this.ParameterType with get() = typeof<string>
                            override this.Position with get() = 0
                            override this.Attributes with get() = ParameterAttributes.Optional
                            override this.DefaultValue with get() = "" :> _
                            override this.RawDefaultValue with get() = "" :> _
                         }
                [| p |]
            member this.GetGeneratedAssemblyContents(assembly:Assembly) =
                
                if AssemblyStore.ContainsKey assembly then
                    AssemblyStore.[assembly]
                else
                    let bytes = System.IO.File.ReadAllBytes assembly.ManifestModule.FullyQualifiedName
                    AssemblyStore.[assembly] <- bytes
                    bytes

            member __.GetInvokerExpression(methodBase, parameters) = 
                match methodBase with
                    | :? ConstructorInfo as ctor -> let o = ctor.Invoke([||]) in Expr.NewObject(ctor,[])
                    | :? MethodInfo as mi -> 
                            let args = parameters |> Seq.skip 1 |> Seq.cast<Expr> |> List.ofSeq
                            Expr.Call(parameters.[0], mi, args)
                    | _ ->  System.IO.File.WriteAllText(@"C:\Users\N\Downloads\error.txt",sprintf "Not supported %A" methodBase)
                            failwith ""
                
            member this.Dispose() = ()
            [<CLIEvent>]
            member this.Invalidate = invalidation.Publish

    (*
    [<TypeProvider>]
    type GenericProvider(config : TypeProviderConfig) as this =
        inherit TypeProviderForNamespaces()
        let ns = "Generics.Provided"
        let asm = Assembly.GetExecutingAssembly()
        //let runtimeAsm = Assembly.LoadFrom(config.RuntimeAssembly)

        let createTypes(genericMethodName, args, typeName) = 

            let elemType = ProvidedTypeDefinition(asm, ns, typeName, Some typeof<obj>)
            let innerType = new ProvidedTypeDefinition (genericMethodName, Some typeof<Extensible>)
            //elemType.IsErased <- false
            //innerType.IsErased <- false

            //innerType.SetAttributes(TypeAttributes.AutoLayout ||| TypeAttributes.AnsiClass ||| TypeAttributes.Class ||| TypeAttributes.Public ||| TypeAttributes.Serializable ||| TypeAttributes.BeforeFieldInit ||| TypeAttributes.Abstract)
            //innerType.SetAttributes(TypeAttributes.Class)
            //innerType.SetAttributes(TypeAttributes.Abstract)
            let ctor = ProvidedConstructor(parameters=[], InvokeCode = fun _ -> <@@ Extensible() @@>)
            //SetAttribute(TypeAttributes.Abstract)
            innerType.AddMember(ctor)

            let args ty = List.init (args + 1) (fun i -> if i = 0 then ProvidedParameter("Meta", ty) else ProvidedParameter(i.ToString(), typeof<obj>))
            let mkGMethod ty = 
                let m = ProvidedMethod(genericMethodName, args ty, typeof<obj>)
                m
            innerType.AddMembers(
                seq{
                    
                    let baseM = mkGMethod typeof<Meta>
                    yield baseM

                    let aux = [typeof<K<obj>>; typeof<R<Meta,Meta>>; typeof<L<Meta,Meta>>; typeof<Prod<Meta,Meta>>; typeof<U>; typeof<Id<obj>>]
                                |> List.map mkGMethod 
                                
                    //aux |> List.iter (fun m -> m.AddMethodAttrs(MethodAttributes.Abstract))
                                
                    for m in aux do
                        yield m
                } |> List.ofSeq
            )
            elemType.AddMember innerType
            elemType
    
        let genericType = ProvidedTypeDefinition(asm, ns, "Imp", Some(typeof<obj>), HideObjectMethods = true)
        let genericMethod = ProvidedStaticParameter("GenericMethodName", typeof<string>)
        let genericMethodArgsCount = ProvidedStaticParameter("Args", typeof<int>)

        do genericType.DefineStaticParameters([ genericMethod; genericMethodArgsCount ], fun typeName args ->
            createTypes(args.[0] :?> string, args.[1] :?> int, typeName)
        )

        do this.AddNamespace(ns,[genericType])
        *)
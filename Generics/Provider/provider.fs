﻿namespace Generics

open System
open System.Reflection
open Microsoft.FSharp.Core.CompilerServices
open Microsoft.FSharp.Quotations
//open Samples.FSharp.ProvidedTypes
open Generics.Rep
open System.Globalization
open ILMerging

[<assembly:TypeProviderAssembly>] 
do()

module Provider =

    let unwords (s : seq<string>) = Seq.fold (fun s w -> sprintf "%s %s" s w) "" s

    let ilMerge = @"X:\Documents\FSharp-Generics\Generics\packages\ilmerge.2.14.1208\tools\ILMerge.exe"

    let mergeAssemblies dup asms =
      let dll = System.IO.Path.GetTempFileName().Replace(".tmp",".dll")
      let dups = dup |> List.map (fun (t : Type) -> sprintf "/allowDup:%s" t.Name) |> unwords
      let files = 
        asms
        |> List.map (fun (a:Assembly) -> sprintf "\"%s\"" a.ManifestModule.FullyQualifiedName)
        |> Set.ofList
        |> unwords

      let psi = System.Diagnostics.ProcessStartInfo(ilMerge,sprintf "/t:library %s /out:\"%s\" %s" dups dll files)
      psi.UseShellExecute <- false
      psi.CreateNoWindow <- true
      let p = System.Diagnostics.Process.Start psi
      p.Start() |> ignore
      p.WaitForExit()
      dll
   
    let concatWith sep' vals' =
        if Seq.length vals' = 0 then
            ""
        else
            Seq.fold (fun s x -> sprintf "%s%s%s" s sep' x) (Seq.head vals') (Seq.skip 1 vals')

    let errorsLog = @"/tmp/errors.log"

    let srcFile = @"/tmp/source.c"

    //let libAsm = @"/home/neto/Documents/FSharp-Generics/Generics/Core/bin/Debug/Generics.dll"
    let libAsm = @"X:\Documents\FSharp-Generics\Generics\Core\bin\Debug\Generics.dll"
    
    //let fSharpCore = @"/home/neto/Documents/FSharp-Generics/Generics/bin/Debug/FSharp.Core.dll"
    let fSharpCore = @"C:\Program Files\Reference Assemblies\Microsoft\FSharp\.NETFramework\v4.0\4.3.1.0\FSharp.Core.dll"


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
                | e -> System.IO.File.WriteAllText(errorsLog,sprintf "Err %A with %A %A %A" e call tys args)
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
    
    let ``c#Name`` (t : Type) = t.FullName.Replace("+",".")
      
    type GenericClassBuilder = {
      methodArgs : Type []
      methodName : string
      retType : Type
      ``namespace`` : string
      ``class`` : string
    } with
      member x.MethodArgs = Array.map ``c#Name`` x.methodArgs
      member x.RetType = ``c#Name`` x.retType
      member x.ArgsValuesName with get () = x.MethodArgs |> Array.mapi (fun i _ -> sprintf "arg_%i" i)
      member x.Args with get () = 
        if x.methodArgs.Length = 0 then
          ""
        else
          Array.zip x.MethodArgs x.ArgsValuesName |> Array.fold (fun s (v,ty) -> sprintf "%s,%s %s" s ty v) ","
      member x.ArgsValueFlat = Array.fold (fun s v -> sprintf "%s,%s" s v) "" x.ArgsValuesName
      member x.ArgsValues = if x.methodArgs.Length = 0 then "" else "," + x.ArgsValueFlat
      member x.ArgTypes =
        if x.MethodArgs.Length = 0 then
          ""
        else
          x.MethodArgs |> Array.fold (sprintf "%s,%s") ","
      member x.Elements = [
        "{{retType}}", x.RetType
        "{{method}}", x.methodName
        "{{methodArgs}}",x.Args
        "{{methodArgsValues}}",x.ArgsValues
        "{{className}}",x.``class``
        "{{namespace}}",x.``namespace`` 
        "{{typeArgs}}",x.ArgTypes
        "{{methodArgsValuesFlat}}",x.ArgsValueFlat
        "{{basePrefix}}",Generics.Selector.basePrefix
        ]
      member x.MakeClass = 
        let v0 = """
          namespace {{namespace}} {
          using System.Reflection;
          using System;
          using Generics;

            public class {{className}}{
              public class C : Selector.Selector{

                public T Id<T>(T t){return t;}
              }

              public class X : C{
              
              //public class T{}
              
              private Func<Rep.Meta {{typeArgs}}, {{retType}}> catchAll;
              public X(Func<Rep.Meta {{typeArgs}}, {{retType}} > f){this.catchAll = f;}
              public {{retType}} {{method}}{{basePrefix}} (Rep.Meta m {{methodArgs}}) {return this.catchAll(m {{methodArgsValues}});}

              
              public {{retType}} {{method}} (Rep.Meta m {{methodArgs}}){return this.SelectInvoke( "{{method}}" ,m,new Object[]{ {{methodArgsValuesFlat}} });}
              // public T {{method}} <T> (Func<Rep.Meta {{typeArgs}}, T > f,Rep.Meta m){throw new Exception();}
              /*
              public {{retType}} {{method}} <T> (Rep.K<T> k {{methodArgs}} ){ return this.catchAll(k {{methodArgsValues}} );}
              public {{retType}} {{method}} <T> (Rep.SumConstr<T,Rep.Meta,Rep.Meta> s {{methodArgs}}){ return this.catchAll( s {{methodArgsValues}} );}
              public {{retType}} {{method}} <T> (Rep.Id<T> i {{methodArgs}} ){ return this.catchAll(i {{methodArgsValues}} );}
              public {{retType}} {{method}} (Rep.U u {{methodArgs}} ){ return this.catchAll(u {{methodArgsValues}} );}
              public {{retType}} {{method}} (Rep.Prod<Rep.Meta,Rep.Meta> p {{methodArgs}}){ return this.catchAll(p {{methodArgsValues}});}
              */
              }
            }
          }
          """
        x.Elements |> List.fold (fun (s : string) (m,r) -> s.Replace(m,r)) v0


    type Extensible() = inherit obj()

    type Generic() = inherit obj()

    let ns = "Generics.Provided"

    let catchAll = "catchAll"


    let private AssemblyStore = Collections.Generic.Dictionary<Assembly,byte[]>()
    
    let pak = sprintf "Rep.%s"

    let mName = pak "Meta"

    let dual n = sprintf "%s<%s,%s>" n mName mName |> pak

    let sName = sprintf "SumConstr<System.Object,%s,%s>" mName mName |> pak

    let pName = dual "Prod"

    let kName = pak "K<System.Object>"

    let uName = pak "U"

    let iName = pak "Id<System.Object>"

    let repConstrs = [sName;pName;kName;uName;iName]

    let mkMethod mods name constr (args : Type list) (ret : Type) invocation =
        let txtArgs = args |> Seq.mapi (fun i a -> sprintf "%s x%i" (``c#Name`` a) i)
                           |> fun xs -> Seq.concat [[constr] :> seq<_>;xs] 
                           |> concatWith ","
        sprintf "%s %s %s(%s){%s}" mods ret.Name name txtArgs invocation

    let mkDefMethod mods name constr (args : Type list) (ret : Type) =
        let invocation = Seq.mapi (fun i _ -> sprintf "x%i" i) args
                            |> Seq.append ["c1"]
                            |> concatWith ","
                            |> sprintf "return this.%s(%s);" catchAll
        mkMethod mods name (sprintf "%s c1" constr) args ret invocation

    let mkDefGlob mods name (args : Type list) (ret : Type) =
        let invocation = 
            let vars = Seq.mapi (fun i _ -> sprintf "x%i" i) args
            vars
            |> concatWith ","
            |> sprintf "return this.SelectInvoke(\"%s\",c1,new Object[]{%s});" name 

        mkMethod mods name (sprintf "%s c1" mName) args ret invocation

    let mkCatchAllDef (args : Type list) (ret : Type) =
        let txtArgs = Seq.concat [args;[ret]] |> Seq.map (fun t -> ``c#Name`` t) 
                    |> fun x -> Seq.concat [seq [mName];x] |> concatWith ","
        sprintf "private Func<%s> %s;" txtArgs catchAll

    let mkConstr name (args : Type list) ret =
        let txtArgs = Seq.concat [args;[ret]] |> Seq.map (fun t -> ``c#Name`` t) 
                        |> fun x -> Seq.concat [seq [mName];x] |> concatWith ","
        sprintf "public %s(Func<%s> f){this.%s = f;}" name txtArgs catchAll


    let makeCompiledClass className methodName args ret =
        let code =  ({
          methodArgs = args |> Array.ofList
          methodName = methodName
          retType = ret
          ``namespace`` = ns
          ``class`` = className}).MakeClass
        System.IO.File.WriteAllText(srcFile, code)
        let dll = System.IO.Path.GetTempFileName()
        let csc = new Microsoft.CSharp.CSharpCodeProvider()
        let args = System.CodeDom.Compiler.CompilerParameters()
        args.OutputAssembly <- dll
        //args.CompilerOptions <- "/t:library"
        args.CompilerOptions <- sprintf "/t:library /r:\"%s\" /r:\"%s\"" libAsm fSharpCore
        let compiled = csc.CompileAssemblyFromSource(args, [| code |])
        let errs = seq{
            for e in compiled.Errors do
            yield e
        }
        System.IO.File.WriteAllText(errorsLog, errs |> Seq.fold (fun s e -> sprintf "%s%s : %i" s e.ErrorText e.Line + System.Environment.NewLine) "" )

        let asm = compiled.CompiledAssembly
        AssemblyStore.Add(asm,System.IO.File.ReadAllBytes dll)
        (asm.GetType(sprintf "%s.%s" ns "Md"), asm)

    [<TypeProvider>]
    type GenericProvider() =
        let invalidation = new Event<EventHandler, EventArgs>()
        let mutable ty = Map.empty
        let assemblies = ref []
        let mutable compiled = None
        interface IProvidedNamespace with
            member this.ResolveTypeName(typeName) = typeof<Generic>
            member this.NamespaceName with get() = ns
            member this.GetNestedNamespaces() = [| |]
            member this.GetTypes() = 
              [| typeof<Generic> |]
        interface ITypeProvider with
            member this.GetNamespaces() = [| this |]
            member this.ApplyStaticArguments(noArgs,withArgs,args) = 
                match ty |> Map.tryFind noArgs.Name with
                | Some ty' -> GenType(ty',(withArgs.[withArgs.Length - 1])) :> _
                | None ->
                    let ``method`` = args.[0] :?> string
                    let retType = typeof<obj>
                    let argsType = List.init (args.[1] :?> int) (fun _ -> typeof<obj>)
                    let className = withArgs.[withArgs.Length - 1]
                    
                    let (t,asm) = makeCompiledClass className ``method`` argsType retType
                    assemblies := asm :: !assemblies 
                    ty <- ty |> Map.add className t
                    t
            member this.GetStaticParameters(typeWithoutArguments) = 
                let param ``type`` name raw def = {new ParameterInfo() with
                            override x.Name with get() = name
                            override this.ParameterType with get() = ``type``
                            override this.Position with get() = 0
                            override this.Attributes with get() = ParameterAttributes.Optional
                            override this.DefaultValue with get() = def
                            override this.RawDefaultValue with get() = raw
                         }
                [|
                    param typeof<string> "MethodName" "" ""
                    param typeof<int> "NumArgs" 0 0
                |]

            member this.GetGeneratedAssemblyContents(assembly:Assembly) =
              //!assemblies |> List.head |> fun a -> a.ManifestModule.FullyQualifiedName |> System.IO.File.ReadAllBytes
              
              let asms = assembly :: !assemblies
              let dup = Map.toList ty |> List.map (fun (_,t) -> t)
              match compiled with
              | Some (asms',bytes) when asms' = asms -> 
                bytes
              | _ ->
              //let ilm = ILMerge()
                let asm = mergeAssemblies dup asms
                let bytes = System.IO.File.ReadAllBytes asm
                compiled <- Some (asms,bytes)
                bytes
              
              //assembly
              (*
              if AssemblyStore.ContainsKey assembly then
                  AssemblyStore.[assembly]
              else
                  let bytes = System.IO.File.ReadAllBytes assembly.ManifestModule.FullyQualifiedName
                  AssemblyStore.[assembly] <- bytes
                  bytes
              *)
            member __.GetInvokerExpression(methodBase, parameters) = 
                match methodBase with
                    | :? ConstructorInfo as ctor ->
                        Expr.NewObject(ctor,parameters |> List.ofArray)
                    | :? MethodInfo as mi -> 
                            let args = parameters |> Seq.skip 1 |> Seq.cast<Expr> |> List.ofSeq
                            Expr.Call(parameters.[0], mi, args)
                    | _ ->  System.IO.File.WriteAllText(errorsLog,sprintf "Not supported %A" methodBase)
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

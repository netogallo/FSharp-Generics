\documentclass[authoryear,10pt]{sigplanconf}

%lhs2TeX imports -- don't remove!
%include polycode.fmt
%include fsharp.fmt


%% Preamble

\usepackage{amsmath}
\usepackage{listings}

%% TODO notes
\usepackage{color}
\usepackage{ifthen}
\newboolean{showNotes}
\setboolean{showNotes}{true}

\newcommand{\todo}[1]{
\ifthenelse
  {\boolean{showNotes}}
  {\textcolor{red}{\textbf{Todo:~}#1}}
  {}}

\newcommand{\wouter}[1]{
\ifthenelse
  {\boolean{showNotes}}
  {\textcolor{blue}{\textbf{Wouter:~}#1}}
  {}}

\newcommand{\ernesto}[1]{
\ifthenelse
  {\boolean{showNotes}}
  {\textcolor{blue}{\textbf{Ernesto:~}#1}}
  {}}


\newcommand{\Sum}{\mathtt{Sum}}
\newcommand{\Prod}{\mathtt{Prod}}
\newcommand{\Meta}{\mathtt{Meta}}
\newcommand{\K}{\mathtt{K}}
\newcommand{\Id}{\mathtt{Id}}

%% End preamble


\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{CONF 'yy}{Month d--d, 20yy, City, ST, Country} 
\copyrightyear{20yy} 
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm} 
\doi{nnnnnnn.nnnnnnn}

% Uncomment one of the following two, if you are not going for the 
% traditional copyright transfer agreement.

%\exclusivelicense                % ACM gets exclusive license to publish, 
                                  % you retain copyright

%\permissiontopublish             % ACM gets nonexclusive license to publish
                                  % (paid open-access papers, 
                                  % short abstracts)

\title{Generic Programming in F\#}
\subtitle{Datatype generic programming for .NET}

\authorinfo{Ernesto Rodriguez}
           {Utrecht University}
           {e.rodriguez@@students.uu.nl}
\authorinfo{Wouter Swierstra}
           {Utrecht University}
           {w.s.swierstra@@uu.nl}

\maketitle

\begin{abstract}
  The introduction of Datatype Generic programming (DGP)
  \emph{revolutionized} \todo{find a better word for revolutionized}
  functional programming by allowing numerous
  algorithms to be defined by induction over the structure of types
  while still providing type safety. Due to the advanced type system
  requirements for DGP, only a handful of functional languages can
  define generic functions making it inaccessible to most
  programmers. Ordinary languages provide reflection and duck typing
  as a mechanism to specify generic algorithms. These mechanisms are
  usually error prone and verbose. By combining ideas from DGP and
  implementing them through reflection, a type-safe interface to DGP
  has been built for the F\# language. These generic algorithms can be
  accessed by any language running in the .NET platform.
\end{abstract}

\category{CR-number}{subcategory}{third-level}

\keywords
data-type generic programming, reflection, F\#, type providers

\section{Introduction}
It is considered a good practice to avoid code repetition since such
code is more mantainable, less error prone and less boring for 
programers. Unfortunately, type systems have created some tension
to achieve this ideal because, on ocassions, it leads to identical
code that only differs by the type signature.

The problem above has been studied for the case of Algebraic
Data Types (ADTs) \cite{} \todo{Cite papers about GP}. Algorithms
that operate on ADTs typically use \emph{pattern matching} to
implement its behaviour. However, pattern matching does not
behave generically such that an expression that pattern matches
values of one type cannot be used to pattern match values of
another type with identical (not to mention similar) structure.

Effort has been invested to overcome this problem. One approach is
combinator based libraries like Uniplate \cite{uniplate} and SYB\cite{syb}
that specify a small set of simple combinators from which a
family of generic functions can be derived. That way boilerplate
code is only needed to define these basic combinators and
it can usually be done automatically. The second approach
is Datatype Generic Programming (DGP) such as PolyP\cite{polyp}, 
Regular\cite{regular}, Multi-Rec\cite{multirec} or RepLib\cite{replib}. 
In this approach, a single (or several) types are used to define
a type representation to which values of a family of types can
be converted. Algorithms are specified in terms of theese
representations and the library provides the infrastructure
to convert values from/to representations.

In the context of F\# (and .Net in general), the traditional
approach to define algorithms generically is reflection. Although
reflection is very powerful, it defeats the purpose of type
safety since type correctness must entirely be checked dynamically.
Since reflection is too general, it can't offer a general optimization
mechanism and every function specified using reflection must
manually implement some caching mechanism to achieve better performance.

The existence of ADTs in F\# could have the potential to use
generic programming to avoid reflection. This paper presents an
implementation of the DGP approach inspired in regular\cite{regular}.
Unfortunately, F\#'s type system is not as sophisticated as
Haskell's type system so the library had to be adapted to
work with F\#. Examples are presented and the definition of
the |uniplate| combinator is provided to show the expressiveness
of the approach.

\section{Background}
This section introduces the F\# language and the .NET
platform. Inspired by the `Scrap your boilerplate' approach to
datatype generic programming \todo{add citation}, we will define a
function called |IncreaseSalary|, that increases the salary of
every employee in a company. Along the way, we will introduce the
relevant concepts from F\# and .NET; in later sections, we will revise
this definition using our library for generic programming.

\subsection{The F\# Language}
The F\# programming language is a functional language of the ML
family. It aims to combine the advantages of
functional programming and the .NET platform. To do so, the F\# designers
have chosen to support a limited number of features from languages such as Haskell or OCaml, 
while still being able to interface well with other .NET languages.
As a result, the language
has a much simpler type system than Haskell or Scala.
Unlike Scala, F\# performs no type erasure when compiled
to the .NET platform.

Before we can define the |IncreaseSalary| function, we will define the types on which it operates:
\begin{code}
[<AbstractClass>]
type Employee() = class
    abstract Salary : float with get() and set()
    abstract NetSalary : float with get()
  end

type Metadata = 
  {name : string; country : string}

type generic(Staff)(t when t :> Employee) =
  | Empty
  | Member of t*generic(Staff)(t)

type generic(Department)(t when t :> Employee) =
  | Tech of Metadata*generic(Members)(t)
  | HR of Metadata*generic(Members)(t)

type generic(Company)(t when t :> Employee) =
  | Empty
  | Dept of generic(Department)(t)*generic(Company)(t)

type GuatemalanEmployee(salary' : int) = class
    inherit Employee()
    let mutable salary = salary'
    override self.Salary  
      with get() = salary
      and  set(value) = salary := value
    override self.NetSalary 
      with get() = self.Salary / 1.12
  end
\end{code}
This example demonstrates the different type declarations that F\# supports.
Besides records, such as |Metadata|, F\# supports algebraic data types (ADTs)
that should be familiar to functional programmers. For example, |Company|,
|Department| and |Staff| are ADTs. Besides algebraic data types,
F\# also supports classes, such as |Employee| and
|GuatemalanEmployee|. There are several important differences between classes
and data types. Records and data types may be deconstructed through pattern matching 
and are immutable. In .NET terminology, they are \emph{sealed}. In contrast to classes,
there is no possible subtyping relation between data types.
Classes in F\#, on the other hand, 
behave just as in any other object oriented language. They can inherit from
other classes, as is the case for the |GuatemalanEmployee|, and may contain
member functions declared with the |member| keyword. Member
functions always take the object on which they are
invoked as an argument. This is represented by the |self| before the dot.

These data declarations also use generic types and type
constraints. Generic types define data types parametrized by a type
argument.  In this case |Company|, |Department| and
|Staff| accept a single type as argument. In our example, the
type arguments have a type constraint, stating that they must be a
subtype of the |Employee| class. The type constraints are
declared using the |when| keyword.

It is worth pointing out that generic type arguments are constraint to
be of kind |*| (star). This is particularly important limitation
in the context of data type generic programming, as many existing
Haskell libraries rely on higher-kinded polymorphism.

Next, we implement the |IncreaseSalary| function. To do so, we
will begin by defining an auxiliary function called |GMap| that
applies its argument function to every |Employee| of the company:

\begin{code}
type generic(Staff)(t) with
  member self.GMap(f) = 
    match self.with
    | Empty -> Empty
    | Member (m,s) -> Member (f m,s.GMap f)
\end{code}
% type Department<'t> with
%   member self.GMap(f) =
%     match self.with
%     | Tech of meta,staff -> Tech (meta,staff.GMap f)
%     | HR of meta,staff -> HR (meta,staff.GMap f)

% type Company<'t> with
%   member self.GMap(f) =
%     match self.with
%     | Empty -> Empty
%     | Member d,c -> Member(d.GMap f, c.GMap f)
% \end{code}
Here we have chosen to \emph{overload} the |GMap| function,
allowing a function with the same name to be defined for different
types. To overload functions in F\#, they must be defined as a member
function. Member functions can be defined for any type; their
definition is not restricted to the type's definition site. 

Using |GMap|,  the |IncreaseSalary| function can be defined as follows:
% \begin{code}
% type Company<'t> with
%   member self.IncreaseSalary(v) =
%     self.GMap (fun e -> e.Salary $\leftarrow$ e.Salary + v;e)
% \end{code}

In the later sections we will show how the |GMap| function may be
derived automatically from the type definitions we saw
previously. Before doing so, however, we would like to give a brief
overview of some of the relevant features of F\# and the .NET
platform.

\paragraph{Operators} The F\# language has a couple of operators that
are used very often by programmers. Here is the list:
\begin{code}
// Reversed function application (aka. pipeline)
let (|>) x f = f x

// Reversed function composition
let ($\gg$) f g x = g (f x)
\end{code}

\subsection{The .NET platform}
The .NET platform is a common runtime environment, supporting
a family of languages. It implements a very rich type
system, including support for generics. Many operations on types
in F\#, such as casting, are handled by the .NET platform. 

\paragraph{Generics and subtyping}

Similarly, the subtyping relation in F\# is also based on the
implementation in .NET.  We write $\tau_a \succ \tau_b$ to denote that
$\tau_a$ is a subtype of $\tau_b$. The subtyping relation can be
checked statically or dynamically. The notation $\tau_a \succ \tau_b$
will be used for static checks whereas the notation $\tau_a \triangleright \tau_b$
will be used for dynamic checks. Dynamic checks occurr when using reflection
to check wether types can be assigned to values at runtime.

As in most object oriented languages, the .NET subtyping mechanism
allows values to be cast implicitly to any supertype.  The F\#
language uses the keyword |inherit| to denote that a type
inherits from another type. A well-known restriction of this mechanism
is that this cast cannot automatically be applied to generic type
arguments. Put differently, $\tau_a \succ \tau_b\ \not\Rightarrow\
\mathtt{T}{<}\tau_a{>} \ \succ \ \mathtt{T}{<}\tau_b{>}$.

\paragraph{Reflection}

The .NET platform uses an abstract class, |Type|, to represent
all the types that are available. This class is used to define
operations such as casting or instantiating the generic type arguments
of a type. Using the .NET reflection mechanism any value can be
queried for its type dynamically. This information can even be used to
compute new types dynamically.

The |Type| class is not sealed. Languages can extend it with any
information they want. This allows F\# to include specific metadata
about algebraic data types and other F\# specific types in the
|Type| class.  We can use this metadata to query the constructors
of algebraic data type, or even pattern match on the type of those
constructors. It is also possible to use reflection and invoke the
type constructors of an ADT to create values of that type. Doing
so is not type-safe in general, since the information gained through
reflection is only available at run-time. Any errors will cause a
runtime exception. Nevertheless, the reflection mechanism is actively
used in libraries such as FsPickler \cite{FsPickler}, a general
purpose .NET serializer.

% \paragraph{Type Providers}
% One language feature particular to F\# is \emph{type
%   providers}~\cite{typeProviders}. Type providers in F\# define a
% mechanism that allows types to be defined by running code at compile
% time. They where designed to provide typed access to external data
% sources. For example, a type provider could parse the header of a
% files containing comma separated values and generate an type
% describing the columns of the data stored in the file. A type provider
% is invoked as follows:
% \begin{code}
% type T = NameProvider<''MyType'',''AnotherType''>

% // prints ``MyType''
% printf ``%s'' typeof<T.MyType>.Name

% // prints ``AnotherType''
% printf ``%s'' typeof<T.AnotherType>.Name

% \end{code}
% This code calls the type provider |Provider| which generates a
% type that is assigned the type synonym |T|. In the example above,
% the |NameProvider| is a type provider that simply creates a type
% that contains nested types named as the arguments that were passed
% to the provider. As it can be seen, the types created by the type
% provider can be used as ordinary F\# types. The type provider also
% accepts static arguments which are restricted to literal values of
% type |int|, |string| and |bool|. The implementation of
% a type provider is quite involved and requires boilerplate code
% to process the information provided by the F\# compiler. For more
% details, the reader is advised to read \cite{TypeProviderTutorial}.

\section{Type Representations in F\#}
The essence of DGP is to provide an abstraction that is able to treat
values of different types and equivalent structure as equivalent while
still providing type safety. Type representations are used to achieve
that objective. The method used here is similar to the approach from
Regular\cite{Regular} but had to be adapted to cope with two of F\#'s
limitations:
\begin{itemize}
\item Generics of higher kind are not permitted in F\# (nor .NET)
\item Method calls must be resolved statically
\end{itemize}
All type representations are a sub-class of the |Meta| abstract
class. It's main role is imposing type constraints on generics that
are required to be a type-representation. Those constraints serve as
an alternative to typeclass constraints that are used in Regular. For
instance in Regular one might have:
\begin{code}
instance (GenericClass a,GenericClass b) =>
  GenericClass (a `times` b) where
    genericFunction x = ...
\end{code}
which in F\# would translate to a class:
\begin{code}
type GenericClass =
  member self.genericFunction<
    var(a),var(b)  when var(a) :< Meta 
                   and var(b) :< Meta> 
                   (x : Prod<var(a),var(b)>) = ...
\end{code}
and this indicates that |var(a)| and |var(b)| must be a type
representation. Later one will see that the constraints not need to
appear in the signature of |genericFunction| because they are
added to the |Prod| class itself (which is also shown later).

The first sub-class of |Meta| is |SumConstr|. This is used
to represent the possible type constructors that an algebraic data
type has. This type takes three type arguments: |t|,|a| and
|b|. The first one indicates the type that this representation
encodes (or |unit| when it is an intermediate component of a
representation). The |var(a)| argument corresponds to the type
representation of values created by one of the type constructors. The
|b| argument contains the representation of the remaining type
constructors or serves the same role as |var(a)| to represent values
created with the last type constructor. Both |var(a)| and |var(b)|
have the constraint |var(a), var(b) :< Meta|. For
instance suppose one has a type:
\begin{code}
type Elems<var(a)> = Cons of var(a)*Elems<var(a)> 
                   | Val of var(a) 
                   | Nil 
\end{code}
its representation would look like:
\begin{code}
type ElemsRep<var(a)> = SumConstr<
                     Elem<var(a)>,
                     _,SumConstr<_,_,_>>
\end{code}
The second sub-class of |Meta| is |Prod|. This type is used
to represent cases in which a type constructor accepts more than one
argument. The |Prod| type accepts two type arguments: |var(a)|
and |var(b)|. The first argument contains the type representation of
one of the constructor's parameters. The second argument contains the
representation of the remaining constructor's arguments or the type
|U| which is used to denote emptyness. Both |var(a)| and
|var(b)| have the constraint |var(a), var(b) :< Meta|. With this constructor it is possible to fill the
blanks of |ElemsRep| as follows:
\begin{code}
type ElemsRep<var(a)> = SumConstr<
  Elem<var(a)>,
  SumConstr<
    unit,
    Prod<_,Prod<_,U>>,
    SumConstr<
      unit,
      Prod<_,U>,
      U>>>
\end{code}
The third sub-class of |Meta| is |K|. This type is used to
represent a type that is not an ADT. Such types cannot be generically
manipulated with DGP, nevertheless it is possible to write algorithms
that operate on occurrences of a particular type(s) inside a ADT. The
|K| constructor takes a single type argument |var(a)| which
corresponds to the type of its content. Since F\# cannot statically
constrain a type to be or not to be an ADT, |var(a)| has no
constraints. To continue with the example above, the type
|Elem<int>| would be represented as:
\begin{code}
type ElemsRep = SumConstr<
  Elem<int>,
  SumConstr<
    unit,
    Prod<K<int>,Prod<_,U>>,
    SumConstr<
      unit,
      Prod<K<int>,U>,
      U>>>
\end{code}
The fourth sub-class of |Meta| is |Id|. This type is used to
represent recursion within a type. This is necessary otherwise a type
representation would be infinite for recursive ADTs. This type takes a
single type argument which is the same type being
represented. With this addition, |Elem<int>| is now represented
as follows:
\begin{code}
type ElemsRep = SumConstr<
  Elem<int>,
  SumConstr<
    unit,
    Prod<K<int>,Prod<Id<Elem<int>>,U>>,
    SumConstr<
      unit,
      Prod<K<int>,U>,
      U>>>
\end{code}
The last sub-class of |Meta| is |U|. This type is used to
represent an empty argument in a type constructor. That is the reason
the |Nil| constructor is represented as |U| and occurrences
of |Prod| will always have |U| as the second argument of the
innermost |Prod|.
\section{Generic Functions}
The purpose of type representations is to provide an interface that
the programmer can use to define generic functions. In other words is
a language to define what the semantics of such functions are. The
library will then be provided with a generic function definition and
will apply it as appropriate to the values it is provided with.

To show how generic definitions look like, the generic function
|gmap| will be defined. This function accepts as an argument a
function of type $\tau\to\tau$ and applies the function to every value
of type $\tau$ in a ADT. In Regular, a generic function is defined as
a typeclass. In this implementation, they are defined as an ordinary
.NET class:
\begin{code}
type GMap<`t>() = class end
\end{code}
The class has a constructor that takes as argument the function that
will be applied. The first step is dealing with the sum of type
constructors. As explained in the previous section, they are
represented by |SumConstr|:
\begin{code}
member x.gmap<'x>(v : SumConstr<'t,Meta,Meta>
                      ,f : Employee$\rightarrow$Employee) =
  match v with
  | L m $\rightarrow$ SumConstr<'x,Meta,Meta>(
             x.gmap m |> Choice1Of2)
  | R m $\rightarrow$ SumConstr<'x,Meta,Meta>(
             x.gmap m |> Choice2Of2)
\end{code}
Here the active patterns |L| and |R| are used to distinguish
the two possible cases. Nevertheless, |gmap| is simply invoked
recursively and the result is packed inside the same constructor. The
next step is to deal with products. This is handled with the
|Prod| constructor:
\begin{code}
member x.gmap(v : Prod<Meta,Meta>
                 ,f : Employee$\rightarrow$Employee) =
  Prod<Meta,Meta>(
    x.gmap(v.E1),
    x.gmap(v.E2))
\end{code}
The type |Prod| contains the properties |E1| and |E2|
that access each of the elements of the product. Once again,
|gmap| is invoked recursively on those values. Next is the case
for the |K| constructor which contains values. Here is where the
function gets applied:
\begin{code}
member x.gmap(v : K<Employee>) = K(f v.Elem)
\end{code}
The property |Elem| of the |K| constructor returns the value
that is being represented by |K|. Note that this member only
works for fundamental values that have a type that matches the
argument function. Later it will be explained how other instances of
|K| work.

The case for the |Id| constructor is a bit more involved because
|Id| contains a property called |Elem| but the property
contains a value, not a representation. In order to obtain the
representation, the type |generic(Generic)(t)| is provided. This type
contains the members:
\begin{code}
member x.To : 't $\rightarrow$ Meta
member x.From : Meta $\rightarrow$ 't
\end{code}
With that class it is now possible to extract the contents of
|Id|, call the |gmap| function and convert the result back
to the original type. This results in:
% \begin{code}
% member x.gmap(v : Id<'t>
%                  ,f : Employee$\rightarrow$Employee) =
%   let g = Generic<'t>()
%   Id<'t>(x.gmap(
%     g.To c.Elem,f) |> g.From)
% \end{code}
There are still two pieces missing in this generic function. First of
all, the recursive calls are invoking |gmap| of type
$\Meta*\mathtt{Employee}\rightarrow\mathtt{Employee}$ and there is no
overload that matches that type. Secondly, not all cases are
covered. Addressing both of these problems requires some boilerplate
code and validations that cannot be checked by the compiler. To
automate some checks and generate the boilerplate code, a type
provider will be used.
\section{The Generic Type Provider}
In the previous section, the existence of a |gmap| function with
type |Meta -> Meta| was assumed. Since |Meta| is an
abstract class, the actual role of the function is to select the
|gmap| overload that corresponds to the argument provided. The
typeclasses mechanism in Haskell selects the overload by type-level
computations that occur during the type-checking process. However, F\#
lacks such mechanism. To achieve this, reflection is used with the
help of a type provider to make the library easier to use and to
provide some extra static checks. The generic type provider is used as
follows:
\begin{code}
type GMapBase = Generic<''gmap'',1>
\end{code}
The type provider accepts two static arguments. The first one denotes
the name of the generic function and the second one the number of
arguments (besides the type representation) that the generic function
accepts. This produces a type with a method |GMap| of type
$\mathtt{Meta} \to \mathtt{obj}$. This method will be in-charge of
selecting the appropriate overload for the multiple representation
types.
\begin{figure*}
\[
\mathtt{x.Method(g,arg_1:\tau_1,..,arg_n:\tau_n)} =
\left\{
  \begin{array}{ll}
    \mathtt{x.m}(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \mathtt{g} : \Sum<\tau,\Meta,\Meta> \\ & \wedge \exists \mathtt{m} \in \mathtt{x}\ .\ \mathtt{m}\ : \Sum<\tau,\Meta,\Meta>*\tau_1*...*\tau_n \\ & \wedge\ \mathtt{m.Name} \equiv \mathtt{Method} \\
    
    \mathtt{x.m}<\mathtt{[\tau/`t]}>(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \exists \mathtt{m} \in \mathtt{x}\ .\ \mathtt{m}<\mathtt{`t}>\ : \Sum<\mathtt{`t},\Meta,\Meta>*\tau_1*...*\tau_n \\ & \wedge\ \mathtt{m.Name} \equiv \mathtt{Method} \\ &\wedge\ \mathtt{g}\ :\ \Sum<\tau,\Meta,\Meta> \\
    
    \mathtt{x.m}(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \exists \mathtt{m} \in \mathtt{x}\ .\ \mathtt{m}\ :\ \Prod<\Meta,\Meta>*\tau_1*...*\tau_n \\ & \wedge\ \mathtt{m.Name} \equiv \mathtt{Method} \\
    
    \mathtt{x.m}(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \mathtt{g}\ :\ \K<\tau> \\ & \wedge\exists \mathtt{m} \in \mathtt{x}\ .\ \mathtt{m}\ :\ \K<\tau>*\tau_1*...*\tau_n \\ & \wedge\ \mathtt{m.Name} \equiv \mathtt{Method} \\

    \mathtt{x.m}<[\tau/\mathtt{`t}]>(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \exists \mathtt{m} \in \mathtt{x}\ .\ \mathtt{m}\ :\ \K<\mathtt{`t}>*\tau_1*...*\tau_n \\ & \wedge\ \mathtt{m.Name} \equiv \mathtt{Method} \\ & \wedge\ \mathtt{g}\ :\ \K<\tau> \\

    \mathtt{x.m}(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \exists \mathtt{m} \in \mathtt{x}\ .\ \mathtt{m}\ :\ \Id<\tau>*\tau_1*...*\tau_n \\ & \wedge\ \mathtt{m.Name} \equiv \mathtt{Method} \\
  \end{array}
\right.
\]
\caption{Selection criteria of the generic provider when using reflection to select an overload.}
\label{fig:selector}
\end{figure*}

The method overload selection mechanism of |GMap| (or any other
generic method created with the generic provider) is described in
\ref{fig:selector}. In this figure:
\begin{itemize}
\item $\tau$ and $\tau_i$ represent type variables which can be any
  concrete type (like |int| or |string|).
\item |`t| denotes generic types which can be replaced by any
  concrete type. Such replacement is represented by the notation
  $[\tau/\mathtt{`t}]$ meaning replace \verb=`t= with $\tau$.
\item |x| denotes the object on which the methods are being invoked.
\item $\mathtt{v}\ :\ \tau$ denotes the typing relation $\mathtt{v}$ is of type $\tau$.
\item $\mathtt{m}\in\mathtt{x}$ denotes a method |m| of object |x|.
\end{itemize}
This selection mechanism selects a method based on the type of the
representation provided to the generic function (|gmap| in the
running example). The selection mechanism matches methods by type in
order to select the correct overload. The whole process can be
summarized as follows:
\begin{itemize}
\item There exists an overload whose type exactly matches the
  arguments given to the generic function. For example: |gmap| is
  called with a value $\mathtt{v}\ \triangleright\
  \K<\mathtt{Employee}>*\tau_1*..*\tau_n$ and there exists a
  |gmap| overload of type
  $\K<\mathtt{Employee}>*\tau_1*..*\tau_n$.
\item There exists an overload that accepts the same representation
  type and contains a generic type argument. For example: |gmap|
  is called with a value $\mathtt{v}\ \triangleright\
  \K<\mathtt{Employee}>*\tau_1*..*\tau_n$ and there exists a
  |gmap| overload that accepts the type $\K<\mathtt{`t}>*\tau_1*..*\tau_n$
  as argument.
\item No overload matches the rules above.
\end{itemize}
To take care of the last item. The type provider requires that the
provided types as first argument to the constructor a default function
$f:\ \Meta*\tau_1*..*\tau_n\rightarrow \tau$. This function will be invoked when no
overloads are found. The definition now looks as follows:
% \begin{code}
% let defaultAction m f = m

% type GMap<'t>() = class
%   inherit GMapBase(defaultAction)
% end
% \end{code}
This definition (although correct) contains type information whose
origin has still not been explained. Recall that the second static
parameter of the type provider is the number of extra arguments of the
generic function. But how does the type provider know what is the type
of the extra arguments? Unfortunately, currently there is no way to
know so all extra arguments will be of type |obj|. The next
sections will discuss more in depth the problem and possible
solutions. Nevertheless, due to this limitation it is more convenient
to include the function arguments of |gmap| at the class level
for more type safety and define a |gmap| overload of type
$\Meta\rightarrow\Meta$ and use it for recursive calls:
% \begin{code}
% type GMapBase = Generic<''gmap'',0>()

% type GMap<'t,'f>(f : `f$\rightarrow$`f) = class
%     inherit GMapBase(defaultAction)

%     member x.gmap(v : Meta) =
%       x.gmap(v) $?{\triangleright}$ Meta
%   end
% \end{code}
Here $\mathtt{x}\ ?{\triangleright}\ \tau$ is the up-casting operation which
attempts to assign |x| the type $\tau$ and fails if $\mathtt{x}
\not\triangleright\ \tau$. With this definition the function that |gmap| will
apply is provided when the class is instantiated and can now have an
explicit type.
\section{A ``better'' Generic Provider}
In principle, what is wrong with the current generic provider is that
it lacks type information of some types. These types are:
\begin{enumerate}
\item The type of each of the extra arguments accepted by the generic function.
\item The return type of the generic function.
\end{enumerate}
Limitation 1 is not a big problem because it can be partially
eliminated by having the arguments on the class level (as our example)
but limitation 2 would be nice to solve. There are two places where
the type provider could accept type arguments:
\begin{enumerate}
\item As a static parameter during the invocation of the type provider.
\item As a generic type parameter passed to the provided type when invoking the constructor.
\end{enumerate}
Neither option is possible in F\#. Option 1 would allow very powerful
type extensions to the language but would require significant changes
to the implementation of type providers because a |Type| object
would need to be constructed to run the type provider's code. Option 2
which is more feasible has been requested at \cite{genericTypeArgs}
would also benefit type providers in large. For example, one could
modify the SQLProvider \cite{SQLProvider} such that one can specify
how to map database types to .NET types. The provided |GMapBase|
type would have the following interface:
\begin{code}
type GMapBase<`t>(f : Meta$\rightarrow$`t) =
  member GMap : Meta$\rightarrow$`t
\end{code}
and could be used as follows to define the |GMap| class:
\begin{code}
type GMap<`t,`f>(f : `f$\rightarrow$`f) = class
    inherit GMapBase<Meta>(defaultAction)
  end
\end{code}
This imporved type provider is able to
determine that the return type of |gmap|
is |Meta|.
\section{Example}
To further explore the usefulness of the library, some
traditional generic functions will be presented. The
first function is |uniplate|. This function is used
by the uniplate library \cite{uniplate} to define
a whole family of generic functions. It's Haskell
signature is: 
\[
\mathtt{uniplate}:\mathtt{Uniplate\ x}
\Rightarrow \mathtt{x} \rightarrow ([\mathtt{x}],[\mathtt{x}]\rightarrow \mathtt{x})
\]
This function is the only member of the |Uniplate|
type-class. It takes a value as an argument and returns
a list of all the recursive childs with the same type
as the argument and a function that allows to re-construct
a value with the same structure using new childs. The
F\# variant of the function should work as the following
example:
\begin{code}
type Arith =
  | Op of string*Arith*Arith
  | Neg of Arith
  | Val of int
  
let (c,f) = uniplate (Op (``add'',Neg (Val 5),Val 8))
printf ``%A'' c // [Neg (Val 5);Val 8]
printf ``%A'' (f [Val 1;Val 2]) // Op (``add'',Val 1,Val 2)

let (c,f) = uniplate (Val 5)
printf ``%A'' c // []
printf ``%A'' (f []) // Val 5

\end{code}
To define the function, two auxiliary generic functions will be
created. The first one is |Collect| which obtains the list
of recursive childs:
\begin{code}
type CollectBase = Generics.Provided.Generics<''Collect'',0>

type Collect<`t>() =
  inherit CollectBase(fun m$\rightarrow$(([] : `t list) $\triangleright$ obj)

  member x.Collect(m : Meta) =
    base.Collect m ${?}\triangleright$ `t list

  member x.Collect<`x>(c : SumConstr<`x,Meta,Meta>) =
    match c with
    | L m $\rightarrow$ x.Collect m
    | R m $\rightarrow$ x.Collect m

  member x.Collect(c : Prod<Meta,Meta>) =
    List.concat<`t> [x.Collect c.E1;x.Collect c.E2]

  member x.Collect(i : Id<`t>) =
    [i.Elem]
\end{code}
The function is straightforward to understand. Every time
the |Id| constructor is reached, its content is added
to a list. The results of products are simply joined
together into a larger list. An explicit type is given
to the default action (|`t list|) because otherwise
F\# assigns |obj list| as default type to lists of
ambigous type (ie. all lists are a subclass of |obj|).
The second generic function is |Instantiate| which is
defined as follows:
\begin{code}
type InstantiateBase = Generics.Provided.Generic<
  ''Instantiate'',0>

type Instantiate<`t>(values` : `t list) =
  inherit InstantiateBase(fun m $\rightarrow$ m $\triangleright$ obj)
  let mutable values = values`

  let pop () = match values with
                | x::xs $\rightarrow$ values $\leftarrow$ xs;Some x
                | [] $\rightarrow$ None

  member x.Instantiate(m : Meta) =
    base.Instantiate m ${?}\triangleright$ Meta

  member x.Instantiate(
    s : SumConstr<`t,Meta,Meta>) =
    match s with
    | L m $\rightarrow$ SumConstr<`t,Meta,Meta>(
      x.Instantiate m |> Choice1Of2)
    | R m $\rightarrow$ SumConstr<`t,Meta,Meta>(
      x.Instantiate m |> Choice2Of2)

  member x.Instantiate(
    s : SumConstr<unit,Meta,Meta>) =
    match s with
    | L m $\rightarrow$ SumConstr<`t,Meta,Meta>(
      x.Instantiate m |> Choice1Of2)
    | R m $\rightarrow$ SumConstr<`t,Meta,Meta>(
      x.Instantiate m |> Choice2Of2)

  member x.Instantiate(i : Id<`t>) =
    match pop () with
    | Some x $\rightarrow$ Id x
    | None $\rightarrow$ None

\end{code}
This function is provided with a list of values and
when applied to a type representation it will replace
all the recursive values within the representation
by values of the provided list. The overloaded
definition for the |SumConstr| case is necessary.
Recall that the first argument of |SumConstr| is either
the type being represented by the |SumConstr| or
|unit| if that |SumConstr| is a intermediate
representation. Since uniplate only deals with
recursive values that occurr on the first level,
the |SumConstr| where the first argument is different
from |`t| (or the generic type to which |uniplate|
has been applied) should not be recursively traversed.
To wrap both pieces together the |Uniplate| function
is now defined:
\begin{code}
type UniplateBase = Generics.Provided.Generic<
  ''Uniplate'',0>

type Uniplate<`t>() =
  inherit UniplateBase(fun _ $\rightarrow$ 
    failwith ``Invalid representation'')

  member x.Uniplate(s : SumConstr<`t,Meta,Meta>) =
    (Collect().Collect s,
     fun vs $\rightarrow$ Instantiate(vs).Instantiate s)

let uniplate<`t> (x : `t) =
  let up = Uniplate<`t>()
  let g = Generic<`t>()
  x |> g.To |> up.Uniplate
  |> fun (x,f) $\rightarrow$ (x, f $\gg$ g.From)

\end{code}
\appendix
\section{Appendix Title}

This is the text of the appendix, if you need one.

\acks

Acknowledgments, if needed.
% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}

% The bibliography should be embedded for final submission.

\begin{thebibliography}{}
\softraggedright

\bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
P. Q. Smith, and X. Y. Jones. ...reference text...

\end{thebibliography}


\end{document}

% Subtyping rather than sub-typing
% data type vs data types

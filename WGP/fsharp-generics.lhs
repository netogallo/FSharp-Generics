\documentclass[authoryear,10pt]{sigplanconf}

%lhs2TeX imports -- don't remove!
%include polycode.fmt
%include fsharp.fmt


%% Preamble

\usepackage{amsmath}
\usepackage{listings}
\usepackage{caption}
\usepackage{subcaption}
\DeclareCaptionType{copyrightbox}

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


\newcommand{\primed}[1]{'#1}
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

\conferenceinfo{WGP '15}{August 30, 2015, Vancouver, British Columbia, Canada} 
\copyrightyear{2015} 
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm} 
\doi{nnnnnnn.nnnnnnn}

% Uncomment one of the following two, if you are not going for the 
% traditional copyright transfer agreement.

%\exclusivelicense                % ACM gets exclusive license to publish, 
                                  % you retain copyright

%\permissiontopublish             % ACM gets nonexclusive license to publish
                                  % (paid open-access papers, 
                                  % short abstracts)

\title{Data Type Generic Programming in F\#}

\authorinfo{Ernesto Rodriguez}
           {Utrecht University}
           {e.rodriguez@@students.uu.nl}
\authorinfo{Wouter Swierstra}
           {Utrecht University}
           {w.s.swierstra@@uu.nl}

\maketitle

\begin{abstract}
  Datatype Generic programming (DGP) enable programmers to define
  functions by induction over the structure of types on which they
  work. Yet the approach has not been adopted very widely, possibly
  due to the many requirements on a language's type system. This paper
  presents a type-safe library for DGP in F\#, built on top of the
  .NET reflection mechanism, The generic functions defined using this
  library can be called by any other language running on the .NET
  platform.
\end{abstract}

\category{D.1.1}{Applicative (Functional) Programming}{}
\category{D.3.3}{Language constructs and features}{}
\keywords
data-type generic programming, reflection, F\#, type providers

\section{Introduction}

Over the last decade, data type generic programming has emerged as an
powerful mechanism for defining families of functions. In Haskell
alone, there are numerous tools and libraries for data type generic
programming, including amongst others PolyP~\cite{polyp}, Generic
Haskell~\cite{GenericHaskell}, Scrap your boilerplate~\cite{SYB},
RepLib~\cite{RepLib}, Uniplate~\cite{Uniplate},
Regular~\cite{Regular}, Multi-Rec~\cite{MultiRec}, and Instant
Generics~\cite{instant2}.

Many of these libraries are implemented in the same fashion. They
define a \emph{representation type} or \emph{universe} that can be
used to describe some collection of types; a \emph{generic} function
may be defined by induction on the elements of representation
type. Finally, these libraries typically support some form of
conversion between values of algebraic data types and their
corresponding representation. This enables users to call generic
functions on custom data types, without having to implement the
underlying conversions manually.

Yet this approach has not been as widely adopted in other
languages. In this paper, we will attempt to address this by
implementing a library for data type generic programming in F\#. More
specifically, we make the following contributions:

\begin{itemize}
\item The type system of F\# may not be as rich as that of Haskell,
  but there are numerous features, including reflection, subtyping,
  type providers and active patterns that may be used for type-level
  programming in F\#. We will briefly present the F\# features our
  library relies upon before describing its implementation
  (Section~\ref{sec:background}).

\item The heart of our library is a representation type defined using
  the sums-of-products adopted by systems such as Generic
  Haskell~\cite{GenericHaskell} and Regular~\cite{Regular}. We show
  how such a representation type may be implmented in F\#
  (Section~\ref{sec:representation}).

\item Next, we show how generic functions may be defined over this
  representation type (Section~\ref{sec:generic-functions}). As an
  example, we will implement a generic map function.

\item To convert a value to our representation type we rely on several
  more advanced F\# features, such as reflection and type
    providers (Section~\ref{sec:conversion}).

\item Finally, we will show how how functions from other Haskell
  libraries such as Uniplate, may be readily implemented using the
  resulting library (Section~\ref{sec:uniplate}).
\end{itemize}

% \todo{Do we want to make the code available from github? If so, this
%   is usually a good place to mention this.}

\section{Background}
\label{sec:background}
This section introduces the F\# language and the .NET
platform. Inspired by the `Scrap your boilerplate' approach to
datatype generic programming~\cite{SYB}, we will define a function
called |IncreaseSalary|, that increases the salary of every employee
in a company. Along the way, we will introduce the the syntax and
relevant concepts from F\# and .NET. We will provide an alternative
definition of |IncreaseSalary| using our library for generic
programming in the second half of this paper.

\subsection{The F\# Language}
The F\# programming language is a functional language of the ML
family. It aims to combine the advantages of functional programming
and Microsoft's .NET platform. To do so, the F\# designers have
adopted numerous features from languages such as Haskell or OCaml,
without sacrificing the ability to interface well with other .NET
languages.  As a result, the language has a much simpler type system
than Haskell or Scala.  Unlike Scala, however, F\# performs no type
erasure when compiled to the .NET platform.

Before we can define the |IncreaseSalary| function, we will define the types on which it operates:
\begin{code}
AbstractClass
type Employee() = class
    abstract Salary : float with get() and set()
    abstract NetSalary : float with get()
  end

type Metadata = 
  {name : string; country : string}

type generic(Staff)(t when vart :> Employee) =
  | Empty
  | Member of vart*generic(Staff)(t)

type generic(Department)(t when vart :> Employee) =
  | Tech of Metadata*generic(Members)(t)
  | HR of Metadata*generic(Members)(t)

type generic(Company)(t when vart :> Employee) =
  | Empty
  | Dept of generic(Department)(t)*generic(Company)(t)

type GuatemalanEmployee(salary' : int) =
  class
    inherit Employee()
    let mutable salary = salary'
    override self.Salary  
      with get() = salary
      and  set(value) = salary := value
    override self.NetSalary 
      with get() = self.Salary / 1.12
  end
\end{code}
This example demonstrates the different type declarations that F\#
supports.  Besides records, such as |Metadata|, F\# supports algebraic
data types (ADTs) that should be familiar to functional
programmers. For example, |Company|, |Department| and |Staff| are
ADTs. Furthermore, programmers in F\# may define classes, such as
|Employee| and |GuatemalanEmployee|. There are several important
differences between classes and data types. Records and data types may
be deconstructed through pattern matching and are immutable. In .NET
terminology, they are \emph{sealed}. In contrast to classes, there is
no possible subtyping relation between data types.  Classes in F\#, on
the other hand, behave just as in any other object oriented
language. They can inherit from other classes -- in our example the
class |GuatemalanEmployee| inherits from the |Employee| class -- and may
contain member functions declared with the |member| keyword. Member
functions always take the object on which they are invoked as an
argument. This is represented by the |self| before the dot.

These data declarations also use generic types and type
constraints. Generic types define data types parametrized by a type
argument.  In this case |Company|, |Department| and
|Staff| accept a single type as argument. In our example, the
type arguments have a type constraint, stating that they must be a
subtype of the |Employee| class. The type constraints are
declared using the |when| keyword.

It is worth pointing out that generic type arguments are constraint to
be of kind |*|. This is particularly important limitation
in the context of data type generic programming, as many existing
Haskell libraries rely on higher kinds.

Next, we implement the |IncreaseSalary| function. To do so, we
will begin by defining an auxiliary function called |GMap| that
applies its argument function to every |Employee| of the company:

\begin{code}
type generic(Staff)(t) with
  member self.GMap(f) = 
    match self.with
    | Empty -> Empty
    | Member (m,s) -> Member (f m,s.GMap f)

type generic(Department)(t) with
  member self.GMap(f) =
    match self.with
    | Tech of meta,staff -> 
        Tech (meta,staff.GMap f)
    | HR of meta,staff -> 
        HR (meta,staff.GMap f)

type generic(Company)(t) with
  member self.GMap(f) =
    match self.with
    | Empty -> Empty
    | Member d,c -> 
        Member(d.GMap f, c.GMap f)
\end{code}
Here we have chosen to \emph{overload} the |GMap| function, allowing a
function with the same name to be defined for different types. To
overload functions in F\#, they must be defined as a member
function. Note that member functions can be defined for any type --
not just classes. They may also be defined post-hoc, i.e., after the
type has been defined.

Using |GMap|,  the |IncreaseSalary| function can be defined as follows:
\begin{code}
type generic(Company)(t) with
  member self.IncreaseSalary(v) =
    self.GMap (fun e -> e.Salary <- e.Salary + v)
\end{code}

In the later sections we will show how the |GMap| function may be
derived automatically from the type definitions we saw
previously. Before doing so, however, we would like to give a brief
overview of some of the relevant features of F\# and the .NET
platform.

% \paragraph{Operators} The F\# language has a couple of operators that
% are used very often by programmers. Here is the list:
% \begin{code}
% // Reversed function application (aka. pipeline)
% let (|>) x f = f x

% // Reversed function composition
% let ($\gg$) f g x = g (f x)
% \end{code}

%% Wouter: let's introduce these as we encounter them. 
% They are pretty familiar to Haskell programmers, even if they have a
% different name

\subsection{The .NET platform}
The .NET platform is a common runtime environment supporting a family
of languages. It provides languages with a type system that includes
support for generics and reflection. Many operations on types in F\#,
such as casting, are handled by the .NET platform.

\paragraph{Generics and subtyping}

The subtyping relation in F\# is also based on the implementation in
.NET.  We write $\tau_a \succ \tau_b$ to denote that $\tau_a$ is a
subtype of $\tau_b$. \wouter{Is this really the notation used? I'd
  expect the operator to go the other way round} \ernesto{In F\# $t1 :> t2$
  means that t1 is a sub-class of t2. So if I choose to use the 
  operator the way it is done in F\#, it is that way. However, if
  you think the main audience is not F\# related we can switch it
  around and add a footnote saying that in F\# code snippets,
  $t1 \prec t2$ means $t1 :> t2$ and that we chose this convention
  to avoid confusion with traditional notation.}
The subtyping relation can be checked statically or dynamically. The notation
$\tau_a \succ \tau_b$ will be used for static checks whereas the
notation $\tau_a \triangleright \tau_b$ will be used for dynamic
checks. Dynamic checks occurr when using reflection to check whether
types can be assigned to values at runtime.

As in most object oriented languages, the .NET subtyping mechanism
allows values to be cast implicitly to any supertype.  The F\#
language uses the keyword |inherit| to denote that a type
inherits from another type. A well-known restriction of this mechanism
is that this cast cannot automatically be applied to generic type
arguments. Put differently, $\tau_a \succ \tau_b\ \not\Rightarrow\
\mathtt{T}\langle\tau_a\rangle \; \succ \; \mathtt{T}\langle\tau_b\rangle$.

\paragraph{Reflection}

The .NET platform uses an abstract class, |Type|, to represent
all types. This class is used to define
operations such as casting or instantiating the generic type arguments
of a type. Using the .NET reflection mechanism any value can be
queried for its type dynamically. This information can even be used to
compute new types dynamically.

The |Type| class is not sealed. Languages can extend it with any
information they want. This allows F\# to include specific metadata
about algebraic data types and other F\# specific types in the
|Type| class.  We can use this metadata to query the constructors
of algebraic data type, or even to pattern match on the type of those
constructors. It is also possible to use reflection and invoke the
type constructors of an ADT to create values of that type. Doing
so is not type-safe in general, since the information gained through
reflection is only available at run-time. Any errors will cause a
runtime exception. Nevertheless, the reflection mechanism is actively
used in libraries such as FsPickler~\cite{FsPickler}, a general
purpose .NET serializer.

\paragraph{Type Providers}
One language feature particular to F\# is \emph{type
  providers}~\cite{typeProviders}. Type providers in F\# allow types
to be defined by running code at compile time. They were designed to
provide typed access to external data sources, such as a database or
XML file. The type provider generates type declarations at compile
time, allowing you to manipulate of such external data in a type safe
manner. For example, you might define a type provider that parses the
header of a file containing comma separated values and subsequently
generates an type describing the columns of the data stored in that
file. 

Writing your own type providers is fairly technical and we will ignore
many of the implementation details in this paper. We will give a brief
example of how type providers may be invoked in F\#.
\begin{code}
type T = NameProvider<<"TypeA","TypeB">>

-- prints "TypeA"
printf "%s" typeof <<T.TypeA>> .Name

-- prints "AnotherType"
printf "%s" typeof <<T.TypeB>> .Name
\end{code}
Here we define the type |T| to be the result of invoking the type
provider |NameProvider| with two |string| arguments.  The
|NameProvider| is a simple type provider that, given |string|
arguments, creates a type with a field for each
argument. \wouter{Ernesto: could you read this section again? I
  changed a few things and want to make sure I haven't introduced any
  falsehoods. Also, I'm not sure what the type provider is doing
  exactly. What would the type T look like if you wrote it by hand?}

From a users perspective, types genererated by type providers are
indistinguishable from types defined by hand.  The implementation of a
type provider is quite involved and requires boilerplate code to
process the information provided by the F\# compiler. For more
details, the reader is advised to read the existing documentation on
writing type providers~\cite{TypeProviderTutorial}.

\section{Type Representations in F\#}
\label{sec:representation}

The core of most libraries for data type generic programming is a
\emph{representation type} or \emph{universe}, that determines the
types that can be represented and how generic functions are defined. We
will adopt the sums-of-products view of algebraic data types, as
pioneered by Generic Haskell~\cite{GenericHaskell} and libraries such
as Regular~\cite{Regular}.

The type system of F\#, however, is not as expressive as that of
Haskell. In particular, all type variables are necessarily of kind
|*|; furthermore, all calls to overloaded methods must be resolved
statically. For these reasons, we will need to adapt the Haskell
approach slightly.

We will define an abstract class, |Meta|, that can will be used to
define type representations. Its purpose is to impose type constraints
on type variables. These constraints serve as an alternative to
typeclass constraints that are used in Regular. For example, (a slight
variation of) the following instance is defined in the Regular
library:

\begin{code}
instance (GMap f, GMap g) => 
  GMap (f :*: g) where
    gmap f (x :*: y) = ...
\end{code}
In F\#, we cannot abstract over higher-kinds. Instead, we therefore
abstract over first-order type variables of kind |*|, and require
that these types themselves are subtypes of the |Meta| class.

In the remainder of this section, we will present the concrete
subtypes of the |Meta| class defined in our library. The first
subclass of |Meta| is |SumConstr|, used to take the sum of two types.
The |SumConstr| takes three type arguments: |t|,|a| and |b|. The first
one indicates the type that this representation encodes. The remaining
arguments, |vara| and |varb|, are the arguments to the sum type.  Note
that both |vara| and |varb| have the constraint that |vara| and |varb|
are subtypes of the |Meta| class.

\begin{figure*}
\centering
\begin{subfigure}[b]{0.3\textwidth}
\begin{code}
AbstractClass
type Meta() = class end
\end{code}
\begin{code}
type U() =
  class
    inherit Meta()
  end
\end{code}
\begin{code}
type K<<varx>>(elem:varx) =
  class
    inherit Meta()
    member self.Elem 
      with get() = elem
  end
\end{code}
\end{subfigure}
\begin{subfigure}[b]{0.3\textwidth}
\begin{code}
type Id<<vart>>(elem:vart) =
  class
    inherit Meta()
    self.Elem 
      with get() = elem
  end
\end{code}

\begin{code}
type SumConstr<<vart,vara,varb
                when vara :> Meta 
                and varb :> Meta>>(
                elem : Choice<<vara,varb>>) =
  class

    inherit Meta()
    member self.Elem 
      with get() = elem
  end
\end{code}

%% \ernesto{From a DGP point of veiw, meta has no purpose but to be the
%%   type from which all derive. In the implementation, it contains some
%%   methods which are used to do reflection but I don't think they need
%%   to be mentioned here?}
\end{subfigure}
\begin{subfigure}[b]{0.3\textwidth}
\begin{code}
type Prod<<vara,varb
           when vara :> Meta
           and varb :> Meta>>(e1:vara,e2:varb) =
  class
    inherit Meta()
    member self.Elem 
      with get() = e1,e2
    member self.E1 
      with get() = e1
    member self.E2 
      with get() = e2
  end
\end{code}
\end{subfigure}
%\begin{subfigure}[b]{0.3\textwidth}
%\end{subfigure}
\caption{Definition in F\# of all the types used to build type representations.}
\label{fig:rep-def}
\end{figure*}

\wouter{Why are they called SumConstr and Prod? Why not just Sum and Prod?}
\ernesto{I agree it should be just Sum. It is bc the original implementation
  contained two subclasses of Sum, namely L and R but I removed them and well
  I would need to re-factor a lot of code to rename which I was planning to do
  for the finished program but since it's not there yet, I thought for the paper
  I should be consitent with the implementation?}

\wouter{Would it be interesting to give the definition of SumConstr
  and Prod here? It might be interesting to see how this stuff looks
  in F\#.  I've trimmed down the example a bit -- this stuff is very
  familiar to the WGP audience.}

The second subclass of |Meta| is |Prod|, corresponding to the product
of two types. The |Prod| type accepts two type arguments: |vara| and
|varb|. Once again, we require both |vara| and |varb| to be subtypes
of the |Meta| class. Besides products, we will use the class |U :>
Meta| to represent the unit type.

Next, the subclass |K| of |Meta| is used to represent a type that is
not defined to be an algebraic data type. This can be used to
represent primitive types, such as |int| or |float|. The |K|
constructor takes a single type argument |vara| which corresponds to
the type of its content. Since F\# cannot statically constrain a type
to be an algebraic data type or not, |vara| has no constraints. 

Finally, |Id| is the last subclass of |Meta|. This type is used to
represent recursive types. This type takes a single type argument that
may be used to refer recursively to the type being represented.

The definitions of these types are given in Figure~\ref{fig:rep-def}.
This definitions are not complete since the actual implementation
incldues extra code used for reflection which is not relevant when
discussing the universe of types that our library can handle. The full
definition can be found in the source code~\cite{FSharp-Generics-Repo}.

We conclude this section with an example of our type
representation. Given the following algebraic data type in F\#:
\begin{code}
type Elems = Cons of int*Elems
                   | Val of int
                   | Nil 
\end{code}
We can represent this type as a subtype of the |Meta| class as
follows:
\begin{code}
type ElemsRep = 
  SumConstr<<
    Elem<<int>>,
    SumConstr<<
      unit,
      Prod<<K<<int>>,Prod<<Id<<Elem<<int>> >>,U>> >>,
      SumConstr<<
        unit,
        Prod<<K << int >>, U>>,
        U>>,
    U>>
\end{code}
This example shows how |SumConstr| takes three arguments: the first
stores meta-information about the type being represented; the second
two type arguments are the types whose coproduct is formed. There is
some overhead in this representation -- we could simplify the
definition a bit by removing spurious unit types. It is important to
emphasise, however, that these definitions will be
\emph{generated}. To keep the generation simple, we have chosen not to
optimize the representation types.

\section{Generic Functions}
\label{sec:generic-functions}
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
type GMap<<`t>>() = class end
\end{code}
The class has a constructor that takes as argument the function that
will be applied. The first step is dealing with the sum of type
constructors. As explained in the previous section, they are
represented by |SumConstr|:
\begin{code}
member x.gmap<<varx>>(v : SumConstr<<vart,Meta,Meta>>
                      ,f : Employee -> Employee) =
  match v with
  | L m -> SumConstr<<varx,Meta,Meta>>(
             x.gmap m |> Choice1Of2)
  | R m -> SumConstr<<varx,Meta,Meta>>(
             x.gmap m |> Choice2Of2)
\end{code}
Here the active patterns |L| and |R| are used to distinguish
the two possible cases. Nevertheless, |gmap| is simply invoked
recursively and the result is packed inside the same constructor. The
next step is to deal with products. This is handled with the
|Prod| constructor:
\begin{code}
member x.gmap(v : Prod<<Meta,Meta>>
                 ,f : Employee -> Employee) =
  Prod<<Meta,Meta>>(
    x.gmap(v.E1),
    x.gmap(v.E2))
\end{code}
The type |Prod| contains the properties |E1| and |E2|
that access each of the elements of the product. Once again,
|gmap| is invoked recursively on those values. Next is the case
for the |K| constructor which contains values. Here is where the
function gets applied:
\begin{code}
member x.gmap(v : K<<Employee>>) = 
  K(f v.Elem)
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
member x.To : vart -> Meta
member x.From : Meta -> vart
\end{code}
With that class it is now possible to extract the contents of
|Id|, call the |gmap| function and convert the result back
to the original type. This results in:
\begin{code}
member x.gmap(v : Id<<vart>>
                 ,f : Employee -> Employee) =
  let g = Generic<<vart>>()
  Id<<vart>>(x.gmap(
    g.To c.Elem,f) |> g.From)
\end{code}
There are still two pieces missing in this generic function. First of
all, the recursive calls are invoking |gmap| of type
$\Meta*\mathtt{Employee}\rightarrow\mathtt{Employee}$ and there is no
overload that matches that type. Secondly, not all cases are
covered. Addressing both of these problems requires some boilerplate
code and validations that cannot be checked by the compiler. To
automate some checks and generate the boilerplate code, a type
provider will be used.

\section{The Generic Type Provider}
\label{sec:conversion}
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
type GMapBase = Generic<<"gmap",1>>
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
\begin{code}
let defaultAction m f = m

type GMap<<vart>>() = class
  inherit GMapBase(defaultAction)
end
\end{code}
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
\begin{code}
type GMapBase = Generic<<"gmap",0>>()

type GMap<<vart,varf>>(f : varf-> varf) = class
    inherit GMapBase(defaultAction)

    member x.gmap(v : Meta) =
      x.gmap(v) mTrRg Meta
  end
\end{code}
Here $\mathtt{x}\ ?{\triangleright}\ \tau$ is the up-casting operation which
attempts to assign |x| the type $\tau$ and fails if $\mathtt{x}
\not\triangleright\ \tau$. With this definition the function that |gmap| will
apply is provided when the class is instantiated and can now have an
explicit type.
\section{A ``better'' Generic Provider}
\label{sec:better-providers}
In principle, what is wrong with the current generic provider is that
it lacks type information of some types. These types are:
\begin{enumerate}
\item The type of each of the extra arguments accepted by the generic function.
\item The return type of the generic function.
\end{enumerate}
Limitation 1 is not a big problem because it can be partially
eliminated by having the arguments on the class level (as our example)
but limitation 3 would be nice to solve. There are two places where
the type provider could accept type arguments:
\begin{enumerate}
\item As a static parameter of a member function
\item As a static parameter during the invocation of the type provider.
\item As a generic type parameter passed to the provided type when invoking the constructor.
\end{enumerate}
Option 1 is the only one that is currently possible in F\#. An
implementation of the generic provider using that option is in
development but there are some details on how .Net handles generic
argumetns that need to be addressed. In any case, the basic idea
is moving the default action from the constructor of the generic
type to the generic method. Take for instance [GMap] which could
be re-written as follows:
\begin{code}
type GMap<<vart,varf>>(f : varf->varf) = class
  inherit GMapBase<<Meta>>()
  member x.GMap(m) =
    base.GMap<<Meta>>(id,m)
\end{code}
Here the [Meta] type argument provided to the [GMap] call is the
one that determines its return type. In addition, the type of the
first argument ([id]) must accept a value of type [Meta] and produce
a value of the same type as the type argument for [GMap], in this case
[Meta]. This approach is type safe in the sense it no longer requires
unsafe casts.

With option 1, the selection mechanism (described in \ref{sec:conversion})
will never select a method that results in a runtime type error
because it knows what the return type of the generic function should be
because of the extra argument. However, if the user made a type error,
he will not see any warnings, errors or runtime errors indicating
he did. The program will simply call the default action in situations
where the user was expecting a generic method to be called.

Option 2 would allow very powerful type extensions to the language 
but would require significant changes
to the implementation of type providers because a |Type| object
would need to be constructed to run the type provider's code. Option 3
which is more feasible has been requested at \cite{genericTypeArgs}
would also benefit type providers in large. For example, one could
modify the SQLProvider \cite{SQLProvider} such that one can specify
how to map database types to .NET types. The provided |GMapBase|
type would have the following interface:
\begin{code}
type GMapBase<<vart>>(f : Meta->vart) =
  member GMap : Meta->vart
\end{code}
and could be used as follows to define the |GMap| class:
\begin{code}
type GMap<<vart,varf>>(f : varf->varf) = class
    inherit GMapBase<<Meta>>(defaultAction)
  end
\end{code}
This imporved type provider is able to
determine that the return type of |gmap|
is |Meta|. Compared to option 1, this one has the
advantage that the |override| keyword could be used
to define the custom generic methods. That way the
type must match at compile time or an error is porduced
instead of a call to the default function.
\section{Example}
\label{sec:uniplate}
To further explore the usefulness of the library, some
traditional generic functions will be presented. The
first function is |uniplate|. This function is used
by the uniplate library~\cite{Uniplate} to define
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
  
let (c,f) = uniplate (Op ("add",Neg (Val 5),Val 8))
printf ``%A'' c -- [Neg (Val 5);Val 8]
printf ``%A'' (f [Val 1;Val 2]) -- Op ("add",Val 1,Val 2)

let (c,f) = uniplate (Val 5)
printf "%A" c -- []
printf "%A" (f []) -- Val 5

\end{code}
To define the function, two auxiliary generic functions will be
created. The first one is |Collect| which obtains the list
of recursive childs:
\begin{code}
type CollectBase = Generics.Provided.Generics<<"Collect",0>>

type Collect<<vart>>() =
  inherit CollectBase(fun m->(([] : vart list) trRg obj)

  member x.Collect(m : Meta) =
    base.Collect m mTrRg vart list

  member x.Collect<<varx>>(
    c : SumConstr<varx,Meta,Meta>) =
    match c with
    | L m -> x.Collect m
    | R m -> x.Collect m

  member x.Collect(c : Prod<<Meta,Meta>>) =
    List.concat<<vart>> [x.Collect c.E1;x.Collect c.E2]

  member x.Collect(i : Id<<vart>>) =
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
type InstantiateBase = Generics.Provided.Generic<<
  "Instantiate",0>>

type Instantiate<<vart>>(values` : vart list) =
  inherit InstantiateBase(fun m -> m -> obj)
  let mutable values = values`

  let pop () = match values with
                | x::xs -> values <- xs;Some x
                | [] -> None

  member x.Instantiate(m : Meta) =
    base.Instantiate m mTrRg Meta

  member x.Instantiate(
    s : SumConstr<<vart,Meta,Meta>>) =
    match s with
    | L m -> SumConstr<<vart,Meta,Meta>>(
      x.Instantiate m |> Choice1Of2)
    | R m -> SumConstr<<vart,Meta,Meta>>(
      x.Instantiate m |> Choice2Of2)

  member x.Instantiate(
    s : SumConstr<<unit,Meta,Meta>>) =
    match s with
    | L m -> SumConstr<<`t,Meta,Meta>>(
      x.Instantiate m |> Choice1Of2)
    | R m -> SumConstr<<`t,Meta,Meta>>(
      x.Instantiate m |> Choice2Of2)

  member x.Instantiate(i : Id<<vart>>) =
    match pop () with
    | Some x -> Id x
    | None -> failwith "Not enough args"

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
  "Uniplate",0>

type Uniplate<<vart>>() =
  inherit UniplateBase(fun _ ->
    failwith "Invalid representation")

  member x.Uniplate(s : SumConstr<<vart,Meta,Meta>>) =
    (Collect().Collect s,
     fun vs -> Instantiate(vs).Instantiate s)

let uniplate<<vart>> (x : vart) =
  let up = Uniplate<<vart>>()
  let g = Generic<<vart>>()
  x |> g.To |> up.Uniplate
  |> fun (x,f) -> (x, f gg g.From)
\end{code}

% \section{Discussion}

% In the context of F\# (and .NET in general), the traditional
% approach to define algorithms generically is reflection. Although
% reflection is very powerful, it defeats the purpose of type
% safety since type correctness must entirely be checked dynamically.
% Since reflection is too general, it can't offer a general optimization
% mechanism and every function specified using reflection must
% manually implement some caching mechanism to achieve better performance.

% =======
\section{Discussion}
Datatype generic programming is a well tested solid approach
to write generic algorithms. It offers a lot of expressiveness compared
to combinator based libraries but has the cost of being
harder to use and requiring powerful type systems. The approach
has been tested and implemented in F\#. Although safety had
to be compromised due to the absense of type system infrastructure
in F\#, a useful tool could still be produced. Even though
not completely safe, it is more type safe than reflection since
only a minimal part of the algorithms require unchecked
(or dynamically checked) type operations. In practice, it is
much more pleasant having theese unsafe runtime 
operations in F\# than in languages like Haskell or Scala
because the .Net runtime can provide rich information
about how/when/why the operation failed. This would result
in a segmentation fault in Haskell or a stacktrace with
erased types in Scala.

The library is on its first release so no optimizations have
been done (since a stable api is desired first) but it is
clear that DGP opens doors for automated caching of operations
which would need to be done manually with reflection. In particular,
the approach is referentially transparent when it comes to the type
of the arguments. In other words, the same overload will be selected
when the arguments given to the method selector have the same type.
This means reflection only needs to be used once to select the
method and next time a call with the same types is done, the
right method can automatically be dispatched. \todo{Is this
clear or should I rather give an example about how this works?}

Compared to existing DGP libraries, the lack of type system
infrastructure makes it very inconvenient to write a class
of generic functions. Theese are the functions that produce
values out of data. The best example is the \verb+read+ function
from Haskell. The problem is that as the funciton parses the
string, it must generate a representation. But in this library,
all type representations are a subclass of \verb+Meta+ so it is
hard to statically check that the algorithm is correct. A
possible way to address the problem is having a type provider
that can be given a type and it produces a new type that
is the exact type for the representation. Then the \verb+read+
or any other function must produce a representation with
that same type (instead of only a sub-type of \verb+Meta+) and
would be reasonable for the F\# compiler to check the correctness
of the algorithm. Unfortunately, (as pointed out before) type
providers can't accept types as static arguments.
of the algorithm. Unfortunately, type providers can't accept types 
as static arguments (see section~\ref{sec:better-providers}).

\section{Conclusions}
Datatype generic programming was successfully implemented for
the F\# programming languages. In spite of the absecne of
higher-rank polymorphism, it was still possible to reclaim
some of the functionality using reflection aided with
type providers for improved static checks. The result is
a library wich can define various generic functions.

The main advantage of this approach compared to ordinary
reflection is type safety. Even though the implementation
performs many unsafe dynamic type checks, they are masked
behind a type-safe interface. It is not possible that
a generic method is invoked with a representation of
a type that is not supported by the method. Another
minor advantage of this approach is providing a structured
way to specify how the generic methods should be selected
through reflection. This opens opportunities for automatic
optimization since reflection only needs to be used once
and the method selection can be cached automatically.

The main disatvantage of this library compared to other
DTG libraries is the reduced type safety of the approach.
That has practical disatvantages which make it hard to
define generic functions similar to |read|. Although a
type error cannot occur when invoking generic methods and
obtaining the result, the user can still experience 
unexpected behavior if he defines a generic function
with the wrong type. This type error will simply be
ignored by the compiler and the selector and
the default action will be invoked instead of the
desired behavior.

Compared to reflection, this approach is much
less general. In the context of F\#, mutually
recursive types are still not supported. The reason
is that the |Id| constructor would require an
additional type argument for every extra type
in the recursion. Advanced DGP libraries using
advanced type systems have solved the problem
in various ways \cite{multirec}. Generally, the
idea consists of using type level functions to
define types that can be used as indexes for
other types. Then each type of the mutual
recursion can be assigned an index. If type
providers in F\# could produce generic types,
it might be possible to lazyly construct the
types required for every type present in a
mutual recurison. Another advantage of
reflection is that it can be used with
any .Net type. This library only works
for algebraic data types.

Type providers were not designed as a
mechanism to do type level programming.
Nevertheless, their flexibility and the
richness of .Net's type system allow
interesting type features to be implemented
in F\#. This is potential available in type
providers that has not yet been exploited
and could result in useful features for
the F\# language.
% \acks

% Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.
\bibliographystyle{abbrvnat}
\bibliography{references}


\end{document}

% Subtyping rather than sub-typing
% data type vs data types

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lhs2pdf"
%%% End: 



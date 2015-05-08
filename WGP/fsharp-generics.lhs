\documentclass[authoryear,10pt,draft]{sigplanconf}

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
\newboolean{marginNotes}
\setboolean{showNotes}{true}
\setboolean{marginNotes}{false}
\newcommand{\marginNote}[1]{
\ifthenelse
  {\boolean{marginNotes}}
  {\marginpar{#1}}
  {#1}}

\newcommand{\todo}[1]{
\ifthenelse
  {\boolean{showNotes}}
  {\marginNote{\textcolor{red}{\textbf{Todo:~}#1}}}
  {}}

\newcommand{\wouter}[1]{
\ifthenelse
  {\boolean{showNotes}}
  {\marginNote{\textcolor{blue}{\textbf{Wouter:~}#1}}}
  {}}

\newcommand{\ernesto}[1]{
\ifthenelse
  {\boolean{showNotes}}
  {\marginNote{\textcolor{blue}{\textbf{Ernesto:~}#1}}}
  {}}


\newcommand{\primed}[1]{'#1}
\newcommand{\Sum}{\mathtt{Sum}}
\newcommand{\Prod}{\mathtt{Prod}}
\newcommand{\Meta}{\mathtt{Meta}}
\newcommand{\K}{\mathtt{K}}
\newcommand{\Id}{\mathtt{Id}}
\newcommand{\U}{\mathtt{U}}

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
  operate. This paper presents a type-safe library for DGP in F\#,
  built on top of the .NET reflection mechanism. The generic functions
  defined using this library can be called by any other language
  running on the .NET platform. 
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
  and active patterns that may be used for type-level
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
  more advanced F\# features, such as reflection (Section~\ref{sec:conversion}).

\item Finally, we will show how how functions from other Haskell
  libraries such as Uniplate, may be readily implemented using the
  resulting library (Section~\ref{sec:uniplate}).
\end{itemize}

% \todo{Do we want to make the code available from github? If so, this
%   is usually a good place to mention this.}

We hope that porting the ideas from the data type generic programming
community to F\# will pave the way for the wider adoption of these
ideas in other, more mainstream, functional languages such as Scala or
Swift.

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

It is worth pointing out that generic type arguments can only
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
\wouter{Ernesto -- is the code above still right? I remember I changed the
  formatting and may also have changed its semantics}


In the later sections we will show how the |GMap| function may be
derived automatically from the type definitions we saw
previously. Before doing so, however, we would like to give a brief
overview of some of the relevant features of F\# and the .NET
platform.

\subsection{The .NET platform}
The .NET platform is a common runtime environment supporting a family
of languages. It provides languages with a type system that includes
support for generics and reflection. Many operations on types in F\#,
such as casting, are handled by the .NET platform.

\paragraph{Generics and subtyping}

The subtyping relation in F\# is also based on the implementation in
.NET.  We write $\tau_a \prec \tau_b$ 
to denote that $\tau_a$ is a
subtype of $\tau_b$. In F\# such subtyping constraints can be specified in a type,
by writing |varta ::> vartb|. 

In any language running on .NET, it is possible to cast a value to
some other (super)type explicitly. When assigning a type $\tau$ to a
value $x$, it is necessary to check that $x$ is of type $\tau$. In
some cases this check can be done statically for which the notatin $x
\prec \tau$, writen $x :> \tau$ in F\#. In other cases, this check can
only be done dynamically, which we will denote by $x \precsim
\tau$. In F\# $x\ {:}{?}{>}\ \tau$. Dynamic checks are usually
necessary when using reflection. When a dynamic type check
fails it results in a runtime error.

As in most object oriented languages, the .NET subtyping mechanism
allows values to be cast implicitly to any supertype.  The F\#
language uses the keyword |inherit| to denote that a type
inherits from another type. A well-known restriction of this mechanism
is that this cast cannot automatically be applied to generic type
arguments. Put differently, $\tau_a \prec \tau_b\ \not\Rightarrow\
\mathtt{T}\langle\tau_a\rangle \; \prec \; \mathtt{T}\langle\tau_b\rangle$.

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

\wouter{Can we scrap this section If we're not using type
  providers anymore?}

\section{Type Representations in F\#}
\label{sec:representation}

\begin{figure*}
\centering
\begin{subfigure}[t]{0.3\textwidth}
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
\begin{subfigure}[t]{0.3\textwidth}
\begin{code}
type Id<<vart>>(elem:vart) =
  class
    inherit Meta()
    self.Elem 
      with get() = elem
  end
\end{code}

\begin{code}
type Sum<<vart,vara,varb
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
\begin{subfigure}[t]{0.3\textwidth}
\begin{code}
type Prod<<vara,varb
           when vara :> Meta
           and varb :> Meta>>(
           e1:vara,e2:varb) =
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
subclass of |Meta| is |Sum|, that represents the sum of two types.
The |Sum| takes three type arguments: |t|,|a| and |b|. The first one
indicates the type that this representation encodes. The remaining
arguments, |vara| and |varb|, are the arguments to the sum type. The
|Choice| type in F\# is analagous to Haskell's |Either| type. It has
two constructors: |Choice1Of2| and |Choice2Of2|. Note that both |vara|
and |varb| have the constraint that |vara| and |varb| are subtypes of
the |Meta| class. \wouter{Why do we need the t in the Sum type?} \ernesto{
  To distinguish the type (if any) that is represented by that sum. Now that
  I think about it, I guess Meta sould have the `t type argument instead.
  See the uniplate example to understand more}


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
  Sum<<
    Elem<<int>>,
    Sum<<
      unit,
      Prod<<K<<int>>,Prod<<Id<<Elem<<int>> >>,U>> >>,
      Sum<<
        unit,
        Prod<<K << int >>, U>>,
        U>>,
    U>>
\end{code}
\wouter{Can you double check this example? I may have screwed it up during reformatting.} \ernesto{Checked.}

This example shows how the |Sum| type constructor takes three
arguments: the first stores meta-information about the type being
represented; the second two type arguments are the types whose
coproduct is formed. There is some overhead in this representation --
we could simplify the definition a bit by removing spurious unit
types. It is important to emphasise, however, that these definitions
will be \emph{generated} using .NET's reflection mechanism. To keep
the generation process as simple as possible, we have chosen not to
optimize the representation types.

\section{Generic Functions}
\label{sec:generic-functions}
The purpose of type representations is to provide an interface that
the programmer can use to define generic functions. Once a function is
defined on all the subtypes of the |Meta| class, it can be executed on
any value whose type may be modelled using the |Meta| class.

To illustrate how generic functions may be defined, we will define a
generic map operator, |gmap|. This function accepts as an argument a
function of type $\tau\to\tau$ and applies the function to every value
of type $\tau$ in a ADT. In Regular, a generic function is defined as
a typeclass. In our library, we define |GMap| as a .NET class:
\begin{code}
type GMap<<vart>>() = 
  class 
  inherit Monofold<<
    vart,Meta,
    Employee -> Employee>>()
  -- [...] Implementation [...]
  end
\end{code}
\wouter{Should we say that we are defining GMap specifically for
  mapping Employee to Employee functions? Or can we be more general
  and define a version of gmap that is generic in the type of the
  function being applied?}  All classes that define generic functions
inherit from the class |Monofold|. This is an abstract class that
specifies the minimal implementation required to define a generic
function. This minimal implementation consists of a method,
|Monofold|, for all the different subtypes of our |Meta| class. By
overriding these |Monofold| methods in the concrete |GMap| class, we
can then define the desired map operation. The |Monofold| class and
its member functions will explained in detail in Section
\ref{sec:conversion}.

The first method we override in the of |GMap| class handles the |Sum|
type constructor:
\begin{code}
override x.Monofold<<varx>>
  (v : Sum<<vart,Meta,Meta>>
  ,f : Employee -> Employee) =
    match v with
    | L m -> Sum<<varx,Meta,Meta>>(
               x.Monofold(m,f) |> Choice1Of2)
    | R m -> Sum<<varx,Meta,Meta>>(
               x.Monofold(m,f) |> Choice2Of2)
    :> Meta
\end{code}
This example uses several F\# specific constructs:
\begin{itemize}
\item The pipeline ($\!\!\!\!$ | ||> | $\!\!\!\!$) operator is simply reversed function
  application: |x ||> f = f x|.
\item The patterns |L| and |R| are \emph{active patterns}. They are
  simply functions defined in such a way that they can be used to
  distinguish values when pattern matching. Since they are functions
  and not type constructors, the left and right cases of |Sum| must be
  constructed with its class constructor. \wouter{And
    why do we need to use active patterns here? And what are they
    exactly?} \ernesto{We don't. We could pattern match over the
    choice type if we wanted. They are only for convenience. As it says
    there, they are functions that can be used to distinguish values when
    pattern matching. When the function distinguishes a value, it returns
    the relevant parts of the value that are of interest. They however are
    not type constructors. It is a type safe alternative to if-statements. They are
    used a lot in F\# to get an FP feel when using class types.}
\end{itemize}
The definition itself is fairly unremarkable: it pattern matches on
its argument and applies the |Monofold| function to the values
contained in the |Sum| type. It then reconstructs a |Sum| instance
with the results of the recursive call, before casting the result back
to a value of type |Meta|. We then call the |Monofold| method on
values of type |Meta|. We defer the description of the member function
|Monofold : Meta * Employee -> Employee| of the |Monofold| class to
the next section.

The next definition handles products:
\begin{code}
override x.Monofold
  (v : Prod<<Meta,Meta>>
  ,f : Employee -> Employee) =
    Prod<<Meta,Meta>>(
      x.Monofold(v.E1,f),
      x.Monofold(v.E2,f))
    :> Meta
\end{code}
The type |Prod| contains the properties |E1| and |E2|, storing the two
constituent elements of the product. Once again, we recursively invoke
|Monofold| on these values.

The next case handles the type |K<<Employee>>|. This is where the
argument function is applied to the |<<Employee>>|s:
\begin{code}
member x.Monofold(v : K<<Employee>>) = 
  K(f v.Elem) :> Meta
\end{code}
The property |Elem| of the |K| constructor returns the value that is
being represented by |K|. Besides this instance, we will need another
instances handling other possible types, |K<<vart>>|, which we will
revisit later.

The case for the |Id| constructor is a bit more involved. Remember
that |Id| contains a property called |Elem : vart|. This property
contains a value, and not a representation of type |Meta|. In order to
obtain the desired representation, we need to define the type
|generic(Generic)(t)|, containing the following two member functions:
\begin{code}
member x.To : vart -> Meta
member x.From : Meta -> vart
\end{code}
With that class it is now possible to extract the contents of |Id|,
call the |Monofold| function and convert the result back to the original
type. We can define the |Monofold| instance for the
|Id| constructor as follows:
\begin{code}
override x.Monofold
  (v : Id<<vart>>
  ,f : Employee -> Employee) =
    let g = Generic<<vart>>()
    Id<<vart>>(x.Monofold(
      g.To c.Elem,f) |> g.From)
    :> Meta
\end{code}

To complete our definiton we override the following two functions:
\begin{code}
override x.Monofold(u : U,
                   ,f : Employee -> Employee) = u :> Meta

override x.Monofold<<varx>>(k : K<<varx>>
                         ,f : Employee -> Employee) = k :> K<<varx>>
\end{code}
Unit values and constants of some type distinct from |Employee| are
left untouched by |GMap|.

This class contains two definitions for the |K| constructor: one
overrides the generic method |Monofold<<varx>>|; the other defines a
member function on |K<<Employee>>|. The |Monofold| class only requires
the generic definition; but we also add the more specific member
function handling employees. By carefully handling overloaded
functions, we will ensure the most specific choice is always made when
faced with such ambiguity. We will cover the precise rules in greater
detail in the next section.

Using the |GMap : Monofold| class, we can now define the following
|gmap| function:
\begin{code}
member x.gmap(x : vart,
             f : Employee -> Employee) =
    let gen = Generic<<vart>>()
    x.Monofold(gen.To x,f)
    |> gen.From
\end{code}
Calling this function, however, requires dispatching on the
representation type, which is handled by the |Monofold| and its member
function.

\section{The Monofold class}

\wouter{Ernesto -- could you convert the figure 5 to use lhs2TeX --
  that way the paper is a bit more consistent...}
\label{sec:conversion}
\begin{figure*}
\[
\mathtt{x.Monofold(g,a_1:\tau_1,..,a_n:\tau_n)} =
\left\{
  \begin{array}{ll}
    \mathtt{x.Monofold}(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \mathtt{g} : \Sum\langle\tau,\Meta,\Meta\rangle \\ & \wedge \exists\ \mathtt{Monofold}\ \in\ \mathtt{x} : \Sum\langle\tau,\Meta,\Meta\rangle*\tau_1*...*\tau_n \\
    
    \mathtt{x.Monofold}\langle\mathtt{[\tau/`t]}\rangle(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \mathtt{g}\ :\ \Sum\langle\tau,\Meta,\Meta\rangle \\ % & \exists \mathtt{x}.\mathtt{Monofold}<\mathtt{`t}>\ : \Sum<\mathtt{`t},\Meta,\Meta>*\tau_1*...*\tau_n \\
    
    \mathtt{x.Monofold}(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \mathtt{g}\ :\ \Prod\langle\Meta,\Meta\rangle*\tau_1*...*\tau_n \\
    
    \mathtt{x.Monofold}(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \mathtt{g}\ :\ \K\langle\tau\rangle \\ & \wedge\exists\ \mathtt{Monofold}\in\mathtt{x}\ :\ \K\langle\tau\rangle*\tau_1*...*\tau_n \\ 

    \mathtt{x.Monofold}\langle[\tau/\mathtt{`t}]\rangle(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \mathtt{g}\ :\ \K\langle\tau\rangle \\

    \mathtt{x.Monofold}(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \mathtt{g}\ :\ \Id\langle\tau\rangle \\
    \mathtt{x.Monofold}(\mathtt{g},\mathtt{arg_1,..,arg_n}) & \mathtt{g}\ :\ \U \\
  \end{array}
\right.
\]
\caption{Selection criteria of the generic provider when using reflection to select an overload.}
\label{fig:selector}
\end{figure*}

In the previous section, we assumed the existence of a |Monofold|
function with type |Meta * (Employee->Employee) -> Meta|. This function
uses reflection to call the corresponding |Monofold| function for
the concrete subclasses of |Meta|. In Haskell, the resolution of
overloading is handled by the type class mechanism; in F\#, we have
had to implement our own mechanism using reflection.

The dispatching mechanism we have implemented is summarized in
Figure~\ref{fig:selector}. This figure adopts the following
conventions:
\begin{itemize}
\item Greek variables, such as |tau| and |tau_i|, refer to a
  concrete type, such as |int| or |string|.
\item As is conventional in F\#, generic type variables are prefixed
  with an apostrophe, such as |`t|. These type variables may still be
  instantiated to a concrete type. We will use the usual notation for
  substitution, writing |[tau / vart]| when the variable |vart| is
  instantiated to |tau|.
\item By convention, the variable |x| will refer the object on which
  the methods are being invoked.
\item We write |m elem x| to refer to the method |m| of object
  |x|.
\end{itemize}

Since |Monofold| is an abstract class, any concrete subclass requires
a minimal set of methods that ensure the existence of a method for
every possible type representation, i.e., every concrete subclass of
the |Meta| type. The |Monofold| method of the abstract |Monofold|
class essentially calls the method associated with the representation
type it is passed as an argument.

Using .NET's reflection mechanism, we can inspect the type of the
argument passed to the |Monofold| method. If we have exactly the right
method at our disposal, for example when calling |Monofold| on |g :
K<<Employee>>| in our example, we call that |Monofold| instance. Only
when there is no specific match, do we instantiate generic type
variables. For example, our example did not define a |Monofold|
instance for the |K<<int>>| class; when encountering an |int|, we call
the instance for |K<<vart>>|, instantiating |vart| to |int|.

\wouter{So why do sum types take three arguments? I still haven't seen
good motivation...}

For type safety, the |Monofold| class is parametrized by several type
arguments. The type |Monofold <<vart,tau,tau1,...,taun>>| has the
the following type variables:
\begin{itemize}
\item The type |vart| refers to the algebraic data type on which the
  function operates. Values of this type are translated to a generic
  representation, that is later handed off to the |Monofold|
  function. 
\item The type |tau| refers to the return type of all of the generic
  methods. In our |GMap| example, we returned a value of type |Meta|,
  corresponding to the algebraic data type resulting from the map.
\item The remaining type variables, |tau1| ... |taun|, refer to any
  additional parameters of the generic function being defined. In the
  |GMap| function, there is a single argument of type |Empolyee ->
  Employee|.
\end{itemize}
With these types in place, the library can apply a generic function to
any ADT. Furthermore, the definition of a new generic function does
not require any casting or reflection. That functionality is
abstracted away by using a common representation for all types.

\wouter{So where is the conversion from ADT to Meta handled? We
  haven't said this clearly enough yet...}

\section{Limitations of the |Monofold| class}
\label{sec:better-monofold}
A major limitation of the current implementation is that all the
overloads of |Monofold| must return a value of the same type. More
advanced libraries for data type generic programming use some limited
form of dependent types, possibly through type classes or type
families, to enable generic functions to return types of different
values. The |Monofold| class lacks such mechanism as it can be used to
subvert the F\# type system. Consider the following example:
\begin{code}
member x.Monofold(v : K<<Employee>>) = 
  K(f v.Elem) :> Meta
\end{code}
The type checker would not object to changing the
function as follows:
\begin{code}
member x.Monofold(v : K<<Employee>>) = 
  K("I am not an Employee!!") :> Meta
\end{code}
This changes the type of value stored in the |K| constructor. This is
type correct since any instance of |K| is a subtype of
|Meta|. \wouter{Yet what goes wrong? Conversion from meta to adt fails
  dynamically?}

Such errors could be prevented by revisiting the previous definition
of the |Monofold| class, adding an additional type parameters for each
overload:
\begin{code}
type Monofold<<
  vart,  -- Generic\ type
  `m,    -- Return\ type\ of\ the\ Meta\ overload
  `s,    -- Return\ type\ of\ the\ Sum\ overload
  `p,    -- Return\ type\ of\ the\ Prod\ overload
  `i,    -- Return\ type\ of\ the\ Id\ overload
  `k,    -- Return\ type\ of\ the\ K\ overload
  `u,    -- Return\ type\ of\ the\ U\ overload
  >>
\end{code}
However, recursive calls to |Monofold| still expect it to
return a value of type |Meta|.\wouter{Why?} This means that the
generics would need to be constrained to be a
subtype of the |Meta| class. Such constraint is possible,
but the |Monofold| function should be able to return
any type, not just subtypes of |Meta|. We would, ideally, like
to require a more general constraints:
\begin{code}
type Monofold<<
  -- [...]
  when `s :> `m
  and `p :> `m
  and `i :> `m
  and `k :> `m
  and `u :> `m
  >>
\end{code}
Unfortunately, type constraints can only be used to enforce that a
type must be a subclass of a \emph{concrete} type, not a type
variable.

Readers familiar with F\# might also consider type providers as an
alternative approach to the meta-programming required to generate
these types. However, type providers cannot accept types as static
arguments and the provided types have many restrictions (such as
forbidding generic methods) which makes them inapropiate.

\wouter{What about defining a 'real' generic gmap function?}

\section{Case study: uniplate}
\label{sec:uniplate}
To further demonstrate our library, we will implement the |uniplate|
function from the Haskell library with the same name. Using this
function, it is possible to define a broad collection of generic
functions. In Haskell, the |uniplate| function has the following type
signature:

> uniplate : Uniplate a => a -> ([a], [a] -> a)

Given a value as an argument and returns
a list of all the children with the same type
as the argument and a function that allows to re-construct
a value with the same structure using new children. The
F\# variant of the function should work as the following
example:
\begin{code}
type Arith =
  | Op of string*Arith*Arith
  | Neg of Arith
  | Val of int
  
let (c,f) = uniplate (Op ("add",Neg (Val 5),Val 8))
printf "%A" c -- [Neg (Val 5);Val 8]
printf "%A" (f [Val 1;Val 2]) -- Op ("add",Val 1,Val 2)
\end{code}
To define the function, we will define two auxiliary generic
functions. The first is |Collect| which computes the list of
child nodes:
\begin{code}
type Collect<<vart>>() =
  inherit Monofold<<vart,vart list>>()

  member x.Monofold(
    c : Sum<<vart,Meta,Meta>>) =
    match c with
    | L m -> x.Collect m
    | R m -> x.Collect m

  member x.Monofold(
    c : Sum<<unit,Meta,Meta>>) =
    match c with
    | L m -> x.Collect m
    | R m -> x.Collect m

  override x.Monofold<<`x>>(
    s : Sum<<`x,Meta,Meta>>) = []

  override x.Monofold(c : Prod<<Meta,Meta>>) =
    List.concat<<vart>> [x.Collect c.E1;x.Collect c.E2]

  override x.Monofold<<varx>>(_ : K<<varx>>) = []

  override x.Monofold(_ : U) = []

  override x.Monofold(i : Id<<vart>>) =
    [i.Elem]
\end{code}
The function is straightforward to understand. Values of the |Sum|
type are processed recursively; the results of products are combined
by concatenating the resulting lists. Constants and unit types return
an empty list. The only interesting case is that for the |Id| type
constructor, which returns a singleton list with its associated
value. Three overloads for the |Sum| constructor are required but only
two of them (which are identical) do recursion. This is because this
function only collects the direct children that appear in the type
constructors of |vart|. \wouter{I don't understand the explanation
  about |Sum| types}

The second generic function is |Instantiate|, defined as
follows:
\begin{code}

type Instantiate<<vart>>(values` : vart list) =
  inherit Monofold<<vart,Meta>>()
  let mutable values = values`

  let pop () = match values with
                | x::xs -> values <- xs;Some x
                | [] -> None

  member x.Monofold(
    s : Sum<<vart,Meta,Meta>>) =
    match s with
    | L m -> Sum<<vart,Meta,Meta>>(
      x.Monofold m |> Choice1Of2)
    | R m -> Sum<<vart,Meta,Meta>>(
      x.Monofold m |> Choice2Of2)
    :> Meta

  member x.Monofold(
    s : Sum<<unit,Meta,Meta>>) =
    match s with
    | L m -> Sum<<unit,Meta,Meta>>(
      x.Monofold m |> Choice1Of2)
    | R m -> Sum<<unit,Meta,Meta>>(
      x.Monofold m |> Choice2Of2)
    :> Meta

  override x.Monofold(i : Id<<vart>>) =
    match pop () with
    | Some x -> Id x
    | None -> failwith "Not enough args"
    :> Meta
  
  override x.Monofold<<`x>>(s : Sum<<`x,Meta,Meta>>) =
    s :> Meta

  override x.Monofold(p: Prod<<Meta,Meta>>) =
    Prod(x.Monofold p.E1,x.Monofold p.E2) 
    :> Meta

  override x.Monofold(u : Unit) = u :> Meta

  override x.Monofold<<`x>>(k : K<<`x>>) = k :> Meta
\end{code}
This function is provided with a list of values and
when applied to a type representation it will replace
all the recursive values within the representation
by values of the provided list. The overloaded
definition for the |Sum| case is necessary.
Recall that the first argument of |Sum| is either
the type being represented by the |Sum| or
|unit| if that |Sum| is a intermediate
representation. Since uniplate only deals with
recursive values that occur on the first level,
the |Sum| where the first argument is different
from |`t| (or the generic type to which |uniplate|
has been applied) should not be recursively traversed.
To wrap both pieces together the |Uniplate| function
is now defined:
\begin{code}
let uniplate<<vart>> (x : vart) =
  let g = Generic<<vart>>()
  let rep = g.To x
  let xs = rep |> Collect().Monofold
  (xs, \ xs' -> Instantiate<<vart>>(xs').Monofold<<vart>>(rep) |> g.From)
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
of the algorithm. Unfortunately, type
providers can't accept types as static arguments.
of the algorithm. \ernesto{This last statement is 
  still relevant in spite of no longer using
  type providers}

\section{Conclusions}
Datatype generic programming was successfully implemented for
the F\# programming languages. In spite of the absecne of
higher-rank polymorphism, it was still possible to reclaim
some of the functionality using reflection and abstract 
classes to enforce certain static assurances. The result is
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
resulting in the wrong overload of |Monofold| being
selected by the selector.

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



\todo{Fix overfull hboxes}
\todo{Extend bibliograhpy}

% \acks

% Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.
\bibliographystyle{abbrvnat}
\bibliography{references}


\end{document}

% Subtyping rather than sub-typing
% data type vs data types
% avoid the passive voice

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lhs2pdf"
%%% End: 



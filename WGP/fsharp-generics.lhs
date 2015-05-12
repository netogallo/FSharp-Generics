\documentclass[authoryear,10pt,draft]{sigplanconf}

%lhs2TeX imports -- don't remove!
%include polycode.fmt
%include fsharp.fmt


%% Preamble

\usepackage{amsmath}
\usepackage{listings}
\usepackage{caption}
\usepackage{subcaption}
\usepackage{multirow}
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
  {\marginNote{\textcolor{green}{\textbf{Ernesto:~}#1}}}
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

\title{Datatype Generic Programming in F\#}

\authorinfo{Ernesto Rodriguez}
           {Utrecht University}
           {e.rodriguez@@students.uu.nl}
\authorinfo{Wouter Swierstra}
           {Utrecht University}
           {w.s.swierstra@@uu.nl}

\maketitle

\begin{abstract}
  Datatype generic programming enable programmers to define functions
  by induction over the structure of types on which they operate. This
  paper presents a type-safe library for datatype generic programming
  in F\#, built on top of the .NET reflection mechanism. The generic
  functions defined using this library can be called by any other
  language running on the .NET platform.
\end{abstract}

\category{D.1.1}{Applicative (Functional) Programming}{}
\category{D.3.3}{Language constructs and features}{}
\keywords
datatype generic programming, reflection, F\#

\section{Introduction}

Over the last decade, datatype generic programming has emerged as an
powerful mechanism for defining families of functions. In Haskell
alone, there are numerous tools and libraries for datatype generic
programming, including PolyP~\cite{polyp}, Generic
Haskell~\cite{GenericHaskell}, Scrap your boilerplate~\cite{SYB},
RepLib~\cite{RepLib}, Uniplate~\cite{Uniplate},
Regular~\cite{Regular}, Multi-Rec~\cite{multirec}, Instant
Generics~\cite{instant2} and many others.

Many of these libraries are implemented in the same fashion. They
define a \emph{representation type} or \emph{universe} that can be
used to describe some collection of types; a \emph{generic} function
may be defined by induction on the elements of representation
type. Finally, these libraries typically support some form of
conversion between values of algebraic datatypes and their
corresponding representation. This enables users to call generic
functions on custom datatypes, without having to implement the
underlying conversions manually.

Yet this approach has not been as widely adopted in other
languages. In this paper, we will attempt to address this by
implementing a library for data type generic programming in F\# \cite{export:192596}. More
specifically, we make the following contributions:

\begin{itemize}
\item The type system of F\# may not be as rich as that of Haskell,
  but there are numerous features, including reflection, subtyping,
  type providers, and active patterns that may be used for type-level
  programming in F\#. We will briefly present the F\# features our
  library relies upon before describing its implementation
  (Section~\ref{sec:background}).

\item The core of our library is a representation type defined using
  the sums-of-products adopted by systems such as Generic
  Haskell~\cite{GenericHaskell} and Regular~\cite{Regular}. We show
  how such a representation type may be implemented in F\# and how the
  conversion functions relating the values of a datatype to its
  generic representation may be generated automatically
  (Section~\ref{sec:representation}).

\item Next, we show how generic functions may be defined over this
  representation type (Section~\ref{sec:generic-functions}). As an
  example, we will implement a generic map function.

\item Where many Haskell libraries use type classes to implement
  type-based dispatch, F\#'s overloading mechanism is too limited for
  our purposes. To address this, we will implement our own system of
  ad-hoc polymorphism using the .NET reflection mechanism
  (Section~\ref{sec:foldmeta})

\item Finally, we will show how how functions from other Haskell
  libraries such as Uniplate, may be readily implemented using the
  resulting library (Section~\ref{sec:uniplate}).
\end{itemize}

% \todo{Do we want to make the code available from github? If so, this
%   is usually a good place to mention this.}

We hope that porting the ideas from the datatype generic programming
community to F\# will pave the way for the wider adoption of these
ideas in other languages such as C\#, Swift and Scala. \ernesto{Should
  we really say scala here? I mean it has been done in
  \cite{scala-jfp}, in a similar fashion as in Haskell. Wouldn't this
  show that we are not aware of the `relevant` work?}

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

\subsection{The F\# language}
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
    abstract Salary : float with get and set
    abstract NetSalary : float with get
  end

type Metadata = 
  {name : string; country : string}

type generic(Staff)(t when vart :> Employee) =
  | Empty
  | Member of vart*generic(Staff)(t)

type generic(Department)(t when vart :> Employee) =
  | Tech of Metadata*generic(Staff)(t)
  | HR of Metadata*generic(Staff)(t)

type generic(Company)(t when vart :> Employee) =
  | Empty
  | Dept of generic(Department)(t)*generic(Company)(t)

type GuatemalanEmployee(salary' : int) =
  class
    inherit Employee()
    let mutable salary = salary'
    override self.Salary  
      with get() = salary
      and  set(value) = salary <- value
    override self.NetSalary 
      with get() = self.Salary / 1.12
  end
\end{code}
This example demonstrates the different type declarations that F\#
supports.  Besides records, such as |Metadata|, F\# supports algebraic
datatypes (ADTs) that should be familiar to functional
programmers. For example, |Company|, |Department| and |Staff| are
ADTs. Furthermore, programmers in F\# may define classes, such as
|Employee| and |GuatemalanEmployee|. There are several important
differences between classes and datatypes. Records and datatypes may
be deconstructed through pattern matching and are immutable. In .NET
terminology, they are \emph{sealed}. In contrast to classes, there is
no possible subtyping relation between datatypes.  Classes in F\#, on
the other hand, behave just as in any other object oriented
language. They can inherit from other classes -- in our example the
class |GuatemalanEmployee| inherits from the |Employee| class. Both
ADTs and classes may contain member functions (or methods) declared
with the |member| keyword. Member functions always take the object on
which they are invoked as an argument. This is represented by the
|self| before the dot.

These data declarations also use generic types and type
constraints. Generic types define datatypes parameterized by a type
argument.  In this case |Company|, |Department| and
|Staff| accept a single type as argument. In our example, the
type arguments have a type constraint, stating that they must be a
subtype of the |Employee| class. The type constraints are
declared using the |when| keyword.

It is worth pointing out that generic type arguments can only
be of kind |*|. This is particularly important limitation
in the context of datatype generic programming, as many existing
Haskell libraries rely on higher kinds.

Next, we implement the |IncreaseSalary| function. To do so, we
will begin by defining an auxiliary function called |MapEmployee| that
applies its argument function to every |Employee| of the company:

\begin{code}
type generic(Staff)(t) with
  member self.MapEmployee(f) = 
    match self.with
    | Empty -> Empty
    | Member (m,s) -> Member (f m,s.GMap f)

type generic(Department)(t) with
  member self.MapEmployee(f) =
    match self.with
    | Tech of meta,staff -> 
        Tech (meta,staff.GMap f)
    | HR of meta,staff -> 
        HR (meta,staff.GMap f)

type generic(Company)(t) with
  member self.MapEmployee(f) =
    match self.with
    | Empty -> Empty
    | Member d,c -> 
        Member(
          d.MapEmployee f, 
          c.MapEmployee f)
\end{code}
Here we have chosen to \emph{overload} the |MapEmployee| function,
allowing a function with the same name to be defined for different
types. To overload functions in F\#, they must be defined as a member
function. Member functions may be defined post-hoc, i.e., after the
type has been defined.

Using |MapEmployee|,  the |IncreaseSalary| function can be defined as follows:
\begin{code}
type generic(Company)(t) with
  member self.IncreaseSalary(v) =
    self.MapEmpolyee (
      fun e -> e.Salary <- e.Salary + v;e)
\end{code}
Note that the because we have defined the |Employee| type as a class,
it is passed by reference in the |MapEmployee| function. The argument
function we pass to |MapEmployee| mutates the object's |Salary|
property directly and subsequently returns the argument object. This
may not be the intended behavior of a map function, but is a
consequence of the way we have defined our types in this example.

In the later sections we will show how the |MapEmployee| function may
be derived automatically by defining a more general |GMap| function
for the type definitions we saw previously. Before doing so, however,
we would like to give a brief overview of some of the relevant
features of the .NET platform.

\subsection{The .NET platform}
The .NET platform is a common runtime environment supporting a family
of languages. It provides languages with a type system that includes
support for generics and reflection. Many operations on types in F\#,
such as casting, are handled by the .NET platform.

\paragraph{Generics and subtyping}

The .NET platform defines a sub-typing relation which is the one used
by F\#. We write $\tau_a \prec \tau_b$ to denote that $\tau_a$ is a
subtype of $\tau_b$. In F\#, such subtyping constraints can be
specified in a type by writing |varta ::> vartb|.

In any language running on .NET, it is possible to cast a value to
some other (super)type explicitly. When assigning a type $\tau$ to a
value $x$, it is necessary to check that $x$ is of type $\tau$. In
some cases, this check can be done statically. We write $x\prec \tau$
(written $x :> \tau$ in F\#) for statically checked casts. In other
cases, this check can only be done dynamically. We write $x \precsim
\tau$ (in F\# $x\ {:}{?}{>}\ \tau$) for dynamically checked
casts. Dynamic checks are usually necessary when using reflection. If
a dynamic type check fails it results in a runtime error; although the
error is raised as an exception which is recoverable contrary to a
segmentation fault.

As in most object oriented languages, the .NET subtyping mechanism
allows values to be cast implicitly to any super-type.  The F\#
language uses the keyword |inherit| to denote that a type inherits
from another type.  The subtyping relation does not extend
automatically to generic types: that is, the implication $\tau_a \prec
\tau_b\ \Rightarrow\ \mathtt{T}\langle\tau_a\rangle \; \prec \;
\mathtt{T}\langle\tau_b\rangle$ does not hold in general.

\paragraph{Reflection}

To handle all type operations and collect type information, the .NET
platform defines the abstract class |Type|. Instances of the class
|Type| encode all the type information about values. When F\# is
compiled to the .NET intermediate language, CIL, an instance of the
|Type| class is generated for every typed defined in the F\# code. The
.NET platform makes this type information available at runtime. Every
object has the method |GetType| which returns the value of type
|Type|.

The |Type| class is not sealed. Languages can extend it with any
information they want. This allows F\# to include specific metadata
about algebraic datatypes and other F\# specific types in the |Type|
class.  We can use this metadata to query the constructors of an
algebraic datatype, or even to pattern match on the type of those
constructors. It is also possible to use reflection and invoke the
type constructors of an ADT to create values of that type. Doing so is
not type-safe in general, since the information gained through
reflection is only available at run-time. Any errors will cause a
runtime exception. Nevertheless, the reflection mechanism is actively
used in libraries such as FsPickler~\cite{FsPickler}, a general
purpose .NET serializer, or Nancy~\cite{Nancy}, a .NET web framework.

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
type U<<`ty>>() =
  class
    inherit Meta()
  end
\end{code}
\begin{code}
type K<<`ty,varx>>(elem:varx) =
  class
    inherit Meta()
    member self.Elem 
      with get() = elem
  end
\end{code}
\end{subfigure}
\begin{subfigure}[t]{0.3\textwidth}
\begin{code}
type Id<<`ty>>(elem:vart) =
  class
    inherit Meta()
    self.Elem 
      with get() = elem
  end
\end{code}

\begin{code}
type Sum<<`ty,vara,varb
                when vara :> Meta 
                and varb :> Meta(
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
type Prod<<`ty,vara,varb
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

The core of most libraries for datatype generic programming is a
\emph{representation type} or \emph{universe}, that determines the
types that can be represented and how generic functions are defined. We
will adopt the sums-of-products view of algebraic datatypes, as
pioneered by Generic Haskell~\cite{GenericHaskell} and libraries such
as Regular~\cite{Regular}.

The type system of F\#, however, is not as expressive as that of
Haskell. In particular, all type variables are necessarily of kind
|*|; furthermore, all calls to overloaded methods must be resolved in
every call site and cannot depend on how type variables get
instantiated. For these reasons, we will need to adapt the Haskell
approach slightly.

We will define an abstract class, |Meta|, that will be used to define
type representations. Its purpose is to impose type constraints on
type variables. These constraints serve as an alternative to typeclass
constraints that are used in Regular. For example, (a slight variation
of) the following instance is defined in the Regular library:

\begin{code}
instance (GMap f, GMap g) => 
  GMap (f :*: g) where
    gmap f (x :*: y) = ...
\end{code}
Rather than abstracting over higher-kinded type arguments, we will abstract
over first-order type variables of kind |*|, and require that these
types themselves are subtypes of the |Meta| class.

In the remainder of this section, we will present the concrete
subtypes of the |Meta| class defined in our library. All the
sub-classes of the |Meta| class are parameterized by at least one
(phantom) type argument, |`ty|.  This argument is instantiated to the
type from which the representation was produced.

The first sub-class of |Meta| is |Sum|, that represents the sum of two
types.  The |Sum| takes two extra type arguments: |`a| and |`b|. They
indicate the inner instances of |Meta| that they encode and are
contained inside a |Chocie| type. The |Choice| type in F\# is
analogous to Haskell's |Either| type. It has two constructors:
|Choice1Of2| and |Choice2Of2|. Note that both |vara| and |varb| have
the constraint that |vara| and |varb| are sub-types of the |Meta|
class.

%% I rather say two extra arguments instead of three because the
%% first argument is explained at the beggining and is present
%% for all representation
The second sub-class of |Meta| is |Prod|, corresponding to the product
of two types. The |Prod| type accepts two extra type arguments: |vara|
and |varb|. Once again, we require both |vara| and |varb| to be
sub-types of the |Meta| class. Besides products, we will use the class
|U :> Meta| to represent the unit type which takes no extra type
arguments.

Next, the sub-class |K| of |Meta| is used to represent a type that is
not defined to be an algebraic datatype. This can be used to represent
primitive types, such as |int| or |float|. The |K| constructor takes
one extra type arguments, |vara|. The argument corresponds to the type
of its content. Since F\# cannot statically constrain a type to be an
algebraic datatype or not, |vara| has no constraints.

Finally, |Id| is the last sub-class of |Meta|. This type is used to
represent recursive types. This type only takes the |`ty| type
argument used to refer to recursive occurrences of a value of the same
type as the value being represented.

The definitions of these types are given in Figure~\ref{fig:rep-def}.
This definitions are not complete since the actual implementation
contains extra code used for reflection which is not relevant when
discussing the universe of types that our library can handle. The full
definition can be found in the source
code~\cite{FSharp-Generics-Repo}.

We conclude this section with an example of our type
representation. Given the following algebraic datatype in F\#:
\begin{code}
type Elems = Cons of int*Elems
                   | Val of int
                   | Nil 
\end{code}
We can represent this type as a sub-type of the |Meta| class as
follows:
\begin{code}
type ElemsRep = 
  Sum<<
    Elem<<int>>,
    Sum<<
      unit,
      Prod<<Elem<<int>>,K<<Elem<<int>>,int>>,
        Prod<<Id<<Elem<<int>> >>,U<<Elem<<int>> >> >> >>,
      Sum<<
        unit,
        Prod<<K << Elem<<int>>,int >>, U<< Elem<<int>> >> >>,
        U<<Elem<<int>> >> >>,
    U<<Elem<<int>> >> >>
\end{code}

This example shows how the |Sum| type constructor takes three
arguments: the first stores meta-information about the type being
represented; the second two type arguments are the types whose
coproduct is formed. \ernesto{We could remove them w/o compromising
  the integrity of the paper, I only wrote it this way bc that is how
  the current implementation does it. However, there is always space
  to improve. The reason I implemented it that way is for uniformity
  :P} There is some overhead in this representation -- we could
simplify the definition a bit by removing spurious unit types. It is
important to emphasize, however, that these definitions will be
\emph{generated} using .NET's reflection mechanism. To keep the
generation process as simple as possible, we have chosen not to
optimize the representation types.

\subsection*{Generating conversion}
\label{sec:generic-class}
This representation type by itself is not very useful. Before we
consider defining generic functions by induction over the
representation type, we will sketch how we can automatically convert
between F\# data types and their corresponding representation.

Many Haskell libraries for generic programming, such as Regular, use
Template Haskell~\cite{Sheard02templatemeta-programming} to generate these
conversions. Some Haskell compilers have a built-in
mechanism~\cite{GenericDeriving} for these conversions. While F\# does
not have the same facilities for meta-programming as Haskell, we can
use the .NET's reflection mechanism to achieve similar results.

The |Object| class of .NET has a method called |GetType : unit ->
Type| which returns a value that containing all the information about
the type of the value on which it is invoked. Since |Type| is an
abstract class, every .NET hosted language is free to extend the
precise information stored in the |Type| class. This allows the F\#
compiler to include metadata that can be used to query the
(type of the) constructors of any algebraic data type at runtime.

Recall that all .NET objects have a member |GetType|. This member can
be used to obtain type information at runtime which is used to
traverse the |Type| value and generate the necessary conversion
functions. This functionality is implemented by the |Generic<<`t>>|
class with the following members:
\begin{code}
type Generic<<`t>>() =
  member x.To : vart -> Meta
  member x.From : Meta -> vart
\end{code}
Note that these conversions are generated \emph{dynamically}, in
contrast to most Haskell approaches to generic programming. Using
memorization, however, we can record the results of the |Generic| class
and limit the performance penalty that this induces.

\section{Generic functions}
\label{sec:generic-functions}

\begin{figure*}
\begin{code}
AbstractClass
type FoldMeta<`t,varin,`out>()

abstract FoldMeta : Meta * varin -> `out
abstract FoldMeta<<`ty>> : Sum<<`ty,Meta,Meta>> * varin -> `out
abstract FoldMeta<<`ty>> : Prod<<`ty,Meta,Meta>> * varin -> `out
abstract FoldMeta<<`ty,`a>> : K<<`ty,`a>> * varin -> `out
abstract FoldMeta : Id<<`t>> * varin -> `out
abstract FoldMeta<<`ty>> : U<<`ty>> * varin -> `out
\end{code}
\caption{Definition of the |Meta| abstract class for 
  generic functions taking one argument.}
\label{fig:def-meta}
\end{figure*}

The purpose of type representations is to provide an interface that
the programmer can use to define generic functions. Once a function is
defined on all the sub-types of the |Meta| class, it can be executed on
any value whose type may be modeled using the |Meta| class.

To illustrate how generic functions may be defined, we will define a
generic map operator, |gmap|. This function accepts as an argument a
function of type $\tau\to\tau$ and applies the function to every value
of type $\tau$ in a ADT. In Regular, a generic function is defined as
a typeclass. In our library, we define |GMap| as a .NET class:
\begin{code}
type GMap<<`t,`x>>() = 
  class 
  inherit FoldMeta<<
    `t,
    `x -> `x,
    Meta>>()
  -- [...] Implementation [...]
  end
\end{code}
Every generic function in our library is a sub-class of the |FoldMeta|
class.  This is an abstract class that specifies the minimal
implementation required to define a generic function. Its definition
is given in Figure \ref{fig:def-meta}. It contains three type
arguments: |`t| which is the type on which the generic functions are
invoked, |varin| which is the input type of the function, |`x->`x| in
this case, and |`out| which is the return type of the generic
function, in this case |Meta|. 

\ernesto{Is the distinction between `t and `ty clear?} The Meta class specifies the minimum functionality to fold over representations. That is a method for each representation type. Furthermore, all those methods are universally quantified over the representation's type arguments to ensure that a suitable overload is available in every case. The only exception is the |Id| case since it represents recursion, all occurrences of |Id| in a representation are the type it represents. To illustrate why this is necessary, consider invoking the |GMap| function on the |Company| type. This type contains nested |Department| values. This means that the intermediate |Sum| constructors in some cases are of type |Sum<<Department<< _ >>,_,_ >>| and other cases of type |Sum<<Company<< _ >>,_,_ >>| (among others). This means that in order to handle both (and any others), the |`ty| argument of the |Sum| type must be universally quantified. For clarity, this section adopts the convention that |`t| always refers to the type of the value being applied to a generic function and |`ty| universally quantifies over the type that a representation represents.

%% The minimal implementation consists of
%% a method, |FoldMeta|, for all the different subtypes of our |Meta|
%% class. Note that |`t| and |`ty| are distinct type variables. In the
%% |FoldMeta| class, |`t| refers to the type that corresponds to the
%% representation being traversed and |`ty| universially quantifies over
%% any type that an intermediate representation represents. For example
%% consider an instance of |FoldMeta| where |`t| is instantiated to
%% |Company|. Since |Department| is a nested type in |Company| there are
%% some ocassions in which |FoldMeta| will be ivoked with a
%% representation of type |Sum<<Department,_,_>>| and some occassions
%% where it will be invoked with a representation of type
%% |Sum<<Company,_,_>>|. Hence one needs to universally quantify in order
%% for a single function to handle this two (and possibly many other)
%% cases. That is the purpose of |`ty|.

By overriding these |FoldMeta| methods in the concrete |GMap| class,
we can then define the desired map operation. The |FoldMeta| class and
its member functions will explained in detail in Section
\ref{sec:foldmeta}. The first method we override in the of |GMap|
class handles the |Sum| type constructor:
% Type `a does de universal quantification over all
% representable types.
% Type `x is the type parameter given as an argument
% to the GMap function
\begin{code}
override self.FoldMeta<<`ty>>
  (v : Sum<<`ty,Meta,Meta>>
  ,f : `x -> `x) =
    match v.Elem with
    | Choice1Of2 m -> 
      Sum<<`ty,Meta,Meta>>(
      self.FoldMeta(m,f) |> Choice1Of2)
    | Choice2Of2 m -> 
      Sum<<`ty,Meta,Meta>>(
      self.FoldMeta(m,f) |> Choice2Of2)
    :> Meta
\end{code}
This example uses the following F\# specific constructs:
\begin{itemize}
\item the the pipeline operator ($\!\!\!\!$ | ||> | $\!\!\!\!$) which
  is simply reversed function application: |x ||> f = f x|. This is a
  common construct used in F\#, analogous to the (|$|) in Haskell but
  asociates to the left and has its arguments flipped. %$
%% Already explained
%% \item The |Choice| type which has the constructors |Choice1Of2| and
%%   |Choice2Of2|. The type is analogous to the |Either| type in Haskell.
\item The |override| keyword serves the same purpose as |member|
  but the results in a compile time error if no matching |member| is
  found in the super-class.
\end{itemize}
% In this case in this case |self.FoldMeta<<`ty>>| universally
% quantifies over the type variable |`ty|. In some cases, the
% quantification is implicit and the compiler can do it
% automatically. However, when overriding methods with the same name
% and similar signatures, leaving it out can make it ambigous to
% determine the exact method being overriden.  
%
% Wouter: I'm removing this here -- we're kind of assuming alread most
% WGP people can read F#, C#, or Scala type signatures (which I think
% is safe to assume)

The definition itself is fairly unremarkable: it pattern matches on
its argument and applies the |FoldMeta| function to the values
contained in the |Sum| type. It then reconstructs a |Sum| instance
with the results of the recursive call, before casting the result back
to a value of type |Meta|. We then call the |FoldMeta| method on
values of type |Meta|. We defer the description of the member function
|FoldMeta : Meta * varin -> `out| of the |FoldMeta| class to
the next section.

The next definition handles products:
\begin{code}
override x.FoldMeta<<`ty>>
  (v : Prod<<`ty,Meta,Meta>>
  ,f : `x -> `x) =
    Prod<<Meta,Meta>>(
      x.FoldMeta(v.E1,f),
      x.FoldMeta(v.E2,f))
    :> Meta
\end{code}
The type |Prod| contains the properties |E1| and |E2|, storing the two
constituent elements of the product. Once again, we recursively invoke
|FoldMeta| on these values.

Similarly, the definition handling the unit type is unremarkable:
\begin{code}
override x.FoldMeta<<`ty>>(u : U<<`ty>>,
                   ,f : `x -> `x) = u :> Meta

\end{code}

We define two cases to handle the |K| type constructor:
\begin{code}
member x.FoldMeta<<`ty>>(v : K<<`ty,`x>>, f : `x->`x) = 
  K(f v.Elem) :> Meta

override x.FoldMeta<<`ty,`a>>(k : K<<`ty,`a>>
                         ,f : `x -> `x) = k :> Meta

\end{code}
The first definition defines a new member function, that applies the
function |f| to a value of type |`x|. The property |Elem| of the |K|
constructor returns the value of type |`x|, which we pass to |f|,
before casting the result back to a value of type |Meta|. The second
definition overrides the required |FoldMeta| member function on |K|;
this definition leaves the underlying value untouched.

%% There are two definitions for the |K| constructor: one
%% overrides the generic method | FoldMeta<<`ty,`a>> |; the other defines
%% a member function on | K<<`t,`x>> |. Note that the type variable | <<`t>> | will be
%% instantiated when the |GMap| class is instantiated. As a result, when |GMap| is
%% instantiated, the type variable | <<`t>> | will be a concrete type and | <<`a>> | will
%% be a type variable.  The |FoldMeta| class only requires the generic
%% definition; but we also add the more specific member function handling
%% | <<`x>> |. By carefully handling such overloaded functions, we will ensure
%% the most specific choice is always made when faced with 
%% ambiguity. We will cover the precise rules in greater detail in the
%% next section.

The override above can apply the function to non-representable types,
but what if |f : `x->`x| were to be defined for an ADT? We need
additional overloads to deal with that case:
\begin{code}

let mapper (f : `x->`x) (v : Meta) =
  let g = Generic<<`x>>()
  v |> g.From |> f |> g.To

member x.FoldMeta(
  u : U<<`x>>,f : `x->`x) = mapper f u
member x.FoldMeta<<`a>>(
  u : K<<`x,`a>>,f : `x->`x) = mapper f u
member x.FoldMeta(
  p : Prod<<`x,Meta,Meta>>,f : `x->`x) = mapper f p
member x.FoldMeta(
  s : Sum<<`x,Meta,Meta>>,f : `x->`x) = mapper f s

\end{code}
Recall that the all representation types have the |`ty|
argument. These overloads instantiate that argument to |`x|; the type
of the function being mapped. Next they convert the representation
back to the type, apply the function and convert the result back to a
representation.

\ernesto{Tried to make clearer the difference between `t and `ty} The
case for the |Id| constructor is a bit more involved. The |Id| case of
the abstract |FoldMeta| member instantiates the |`ty| argument of the
|Id| constructor to |`t|. This means that the |Id| case only needs to
be specified for the type |`t|, the type to which the generic function
is being applied, instead of universally quantifying over all
types. Recall that |Id| is used to represent recursion within a
type. To do so, it contains the value of the recursive occurrence of
|`t| in itself. That value can be accessed with the |Elem|
property. However, the property contains a value of type |`t| and not
|Meta|, so it cannot be used for recursive calls to |FoldMeta|. With
the |Generic<<`ty>>| class it is possible to extract the contents of
|Id|, call the |FoldMeta| function and convert the result back to the
original type. We can define the |FoldMeta| instance for the |Id|
constructor as follows:

%% Remember that |Id| contains a property called |Elem : `t|. This
%% property contains a value, and not a representation of type |Meta|.
%% With the |Generic<<`ty>>| class it is possible to extract the contents
%% of |Id|, call the |FoldMeta| function and convert the result back to
%% the original type. We can define the |FoldMeta| instance for the |Id|
%% constructor as follows:
\begin{code}
override x.FoldMeta
  (v : Id<<`t>>
  ,f : `x -> `x) =
    let g = Generic<<`t>>()
    Id<<`t>>(x.FoldMeta(
      g.To c.Elem,f) |> g.From)
    :> Meta
\end{code}
Using the |GMap :> FoldMeta| class, we can now define the following
|gmap| function:
\begin{code}
member x.gmap(x : vart,
             f : `x -> `x) =
    let gen = Generic<<`x>>()
    x.FoldMeta(gen.To x,f)
    |> gen.From
\end{code}
Calling this function, however, requires dispatching on the
representation type, which is handled by the |FoldMeta| and its member
function. An instance of |GMap| with | <<`t>> | set to |Company| and |
<<`x>> | set to |Employee| would implement the |MapEmployee| function
introduced in the introduction.

\section{The FoldMeta class}
\label{sec:foldmeta}
% \begin{table*}
% \begin{tabular}{cccc}
%   \multirow{15}{*}{|self.FoldMeta(m : Meta)|} & \multirow{15}{*}{$=\left\{\begin{array}{c} \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \end{array}\right.$} & \multirow{2}{*}{|self.FoldMeta(m)|} & |exists self.FoldMeta : tau->tau1|  \\
%   & & & $\wedge$ |m : tau| \\
%   & & & \\
%   & & \multirow{4}{*}{|self.FoldMeta<<tau_a>>(m.Cast())|} & |self.FoldMeta<<`ty>> : tau'->tau1| \\
%   & & & $\wedge$ |m : tau<<tau_ty,tau_m1,tau_m2>>| \\
%   & & & $\wedge$ |tau_m1 :> Meta| $\wedge$ |tau_m2 :> Meta| \\
%   & & & $\wedge$ |[tau_ty/`ty]tau' = tau<<tau_a,Meta,Meta>>| \\
%   & & & \\
%   & & \multirow{3}{*}{|self.FoldMeta<<tau_a>>(m)|} & |exists self.FoldMeta<<`a>> : tau'->tau1| \\
%   & & & $\wedge$ |m : tau<<tau_ty,tau_a>>|\\
%   & & & $\wedge$ |[tau_a/`a]tau' = tau<<tau_ty,tau_a>>|\\
%   & & & \\
%   & & \multirow{3}{*}{|self.FoldMeta<<tau_ty,tau_a>>(m)|} & |self.FoldMeta<<`ty,`a>> : tau'->tau1| \\
%   & & & $\wedge$ |m : tau<<tau_ty,tau_a>>|\\
%   & & & $\wedge$ |[tau_ty/`t][tau_a/`a]tau' = tau<<tau_ty,tau_a>>|\\
%   & & & \\
%   %% & & | = o.Sum(x : Sum<<tau,Meta,Meta>>,v1 : tau1,...,vn : taun)| \\
%   %% & & |self.Sum(x : Meta,v1 : tau1,...,vn : taun)| \\
%   %% & & | = o.Sum<<tau>>(x : Sum<<tau,Meta,Meta>>,v_1 : tau1,...,v_n : taun)|
% \end{tabular}
% \caption{Selection criteria of the |FoldMeta| class when using reflection to select an overloaded function.
% This is the criteria when |FoldMeta| takes no extra arguments but the selection works the same
% way since only the sub-types of |Meta| are inspected to select the overloaded function as long as the types
% of the extra arguments are consistent.}
% \label{fig:selector}
% \end{table*}

In the previous section, we assumed the existence of a |FoldMeta|
function with type |Meta * (`x->`x) -> Meta|. Before getting into the
details of this function, we would like to revisit the problem that it
needs to solve. Consider the following instances, defining a fragment
of a generic |map| function in Haskell:
\begin{code}
instance (GMap a,GMap b) => 
  GMap (a :+: b) where
  gmap (L a) f = L (gmap a f)
  gmap (R b) f = R (gmap a f)

instance GMap (K x) where
  gmap k _ = k

instance GMap (K Int) where
  gmap (K i) f = K (f i)
\end{code}
The two instance definitions for the type constructor |K|
\emph{overlap}. When invoking |gmap| on a value of type |K Int|, the
second instance is used, even if the first instance would also have
been a valid choice. Haskell extensions that allow overlapping
instances define a precise set of rules specifying which instance
definition should be chosen when there is more than one alternative
available.

We could try to adopt a similar approach in F\#, by defining the
following member functions:
\begin{code}

member x.FoldMeta<<`ty,`a,`b>>(
  s : Sum<<`ty,`a,`b>>, f : int -> int) =
  match s.Elem with
  | Choice1Of2 a -> 
    Sum<<`ty,`a,`b>>(
      x.FoldMeta(a,f) |> Choice1Of2)
  | Choice2Of2 b ->
    Sum<<`ty,`a,`b>>(
      x.FoldMeta(b,f) |> Choice1Of2)

member x.FoldMeta<<`ty,`a>>(
  k : K<<`ty,`a>>,f : int -> int) = k

member x.FoldMeta<<`ty>>(
  k : K<<`ty,int>>,f : int -> int) = K (f k)
\end{code}
However, this code is rejected by the F\# compiler. The |Sum|
constructor makes two a recursive calls. When this function is
defined, it is still unclear how to resolve these recursive calls. In
particular, whether these calls are generic in one, two or three type
variables. As a result, the F\# rejects this definition, even if we
can determine this for any call to |FoldMeta| for a fixed type.

We resolved this problem by defining a |FoldMeta|
function of type |Meta*varin -> `out|.  This function can also be
invoked by the recursive calls of the |Sum| or |Product| constructors,
as these type constructors are parameterized by variables |`a,`b :>
Meta|. This |FoldMeta| function then selects the corresponding
`instance' that should be invoked based on the type of its
argument. Note that this is handled statically in Haskell, but must
necessarily be done dynamically in F\#.

To define the |FoldMeta| function that dispatches based on its
argument's type, we once again use the .NET reflection mechanism. The
|FoldMeta| function inspects the type of its argument. If we have
exactly the right method at our disposal, we invoke that method. We
only instantiate a more generic method when necessary. This ensures
the desired behavior for the two definitions of |GMap| for |K| that
we saw previously.

% For type safety, the |FoldMeta| class is parametrized by several type
% arguments. The type |FoldMeta <<vart,varin1,...,varinn,`out>>|
% consists of the follwing arguments:
% \begin{itemize}
% \item The type |vart| refers to the algebraic datatype on which the
%   function operates. Values of this type are translated to a generic
%   representation, that is later handed off to the |FoldMeta|
%   function.
% \item The type |`out| refers to the return type of all of the generic
%   methods. In our |GMap| example, we returned a value of type |Meta|,
%   corresponding to the algebraic datatype resulting from the map.
% \item The remaining type variables, |varin1| ... |varinn|, refer to
%   any additional parameters of the generic function being defined. In
%   the |GMap| function, there is a single argument of type |`x ->
%   `x|. Types in F\# must take a specific number of arguments but
%   the language allows multiple types with the same name to be
%   defined. So a variants of |FoldMeta| are defined taking from 0 to 5
%   input type argumetns.
% \end{itemize}
% The |FoldMeta| class provides a default implementation of the
% |FoldMeta| member of type |Meta*varin1*...*varinn -> out|. This member
% implements the dispatching mechanism described above which is outlined
% in Figure~\ref{fig:selector}. This figure adopts the following
% conventions:
% \begin{itemize}
% \item Greek variables, such as |tau| and |tau_i|, refer to a
%   concrete type, such as |int| or |string|. They can be contrete
%   types that take generic arguments such as |K<<`t,`a>>|.
% \item As is conventional in F\#, generic type variables are prefixed
%   with an apostrophe, such as |`t|. These type variables may still be
%   instantiated to a concrete type. We will use the usual notation for
%   substitution, writing |[tau / vart]tau'| when the variable |vart| is
%   instantiated to |tau| in type |tau'|.
% \item By convention, the variable |self| will refer the object on which
%   the methods are being invoked.
% \item The |exists self.FoldMeta : tau| indicates a case were an
%   implementation of |FoldMeta| with type |tau| is optional, in other
%   words it's not an abstract member of the |FoldMeta| abstract
%   class. Conversly, when the the overload is a required to be defined
%   in the abstract class, we omit the |exists| and only write
%   |o.FoldMeta : tau|.
% \item For the |Sum| and |Prod| case, a member function called |Cast|
%   is invoked. This function is necessary because |tau<<tau_ty,tau_m1,tau_m2>> !:> tau<<tau_ty,Meta,Meta>>| in spite of |tau_m1:>Meta| and |tau_m2:>Meta|. This function is defined below.
% \end{itemize}
% \begin{code}
% type Sum<<`ty,`a,`b>> with
%   member Cast : unit -> Sum<<`t,Meta,Meta>>
%   member x.Cast() = 
%   match x.Elem with
%   | Choice1Of2 m -> 
%     Sum<<`ty,Meta,Meta>>(
%       Choice1Of2 (m :> Meta))
%   | Choice2Of2 m -> 
%     Sum<<`ty,Meta,Meta>>(
%       Choice2Of2 (m :> Meta))
% \end{code}
% \begin{code}
% type Prod<<`ty,`a,`b>> with
%   member Cast : unit -> Prod<<`t,Meta,Meta>>
%   member x.Cast() = 
%     Prod<<`ty,Meta,Meta>>(
%      x.E1 :> Meta,x.E2 :> Meta)
% \end{code}
% \ernesto{Maybe only the type is necessary and not the implementation.}
% Since |FoldMeta| is an abstract class, any concrete subclass requires
% a minimal set of methods that ensure the existence of a method for
% every possible type representation, i.e., every concrete subsclass of
% the |Meta| type. The |FoldMeta| method of the abstract |FoldMeta|
% class essentially calls the method associated with the representation
% type it is passed as an argument.


With these types in place, the library can apply a generic function to
any ADT. Furthermore, the definition of a new generic function does
not require any casting or reflection. That functionality is
abstracted away by using a common representation for all types.

\section{Case study: Uniplate}
\label{sec:uniplate}
To further demonstrate how generic functions may be defined using our
library, we will implement the |uniplate| function from the Haskell
library with the same name. In Haskell, the |uniplate| function has
the following type signature:

> uniplate : Uniplate a => a -> ([a], [a] -> a)

Given an argument of type |a|, the |uniplate| function returns a list
of all the immediate child nodes of type |a| and a function that can
be used to reassemble the original value, given a list of child
nodes. The F\# version of |uniplate|, that we will define shortly,
should work as follows:
\begin{code}
type Arith =
  | Op of string*Arith*Arith
  | Neg of Arith
  | Val of int
  
let (c,f) = uniplate (
  Op ("add",Neg (Val 5),Val 8))
-- prints [Neg (Val 5);Val 8]
printf "%A" c
-- prints Op ("add",Val 1,Val 2)
printf "%A" (f [Val 1;Val 2]) 
\end{code}
To define the function, we will define two auxiliary generic
functions. The first is |Collect| which computes the list of
child nodes:
\begin{code}
type Collect<<vart>>() =
  inherit FoldMeta<<vart,vart list>>()

  member self.FoldMeta<<`ty>>(
    c : Sum<<`ty,Meta,Meta>>) =
    match c with
    | L m -> self.Collect m
    | R m -> self.Collect m

  override self.FoldMeta<<`ty>>(
    c : Prod<<`ty,Meta,Meta>>) =
    List.concat<<vart>> [
      self.Collect c.E1
      ;self.Collect c.E2]

  override self.FoldMeta<<`ty,`a>>(
    _ : K<<`ty,`a>>) = []

  override self.FoldMeta<<`ty>>(_ : U<<`ty>>) = []

  override self.FoldMeta(i : Id<<vart>>) =
    [i.Elem]
\end{code}
The function is straightforward to understand. Values of the |Sum|
type are processed recursively; the results of products are combined
by concatenating the resulting lists. Constants and unit types return
an empty list. The only interesting case is that for the |Id| type
constructor, which returns a singleton list with its associated
value. An important remark is that the |FoldMeta| class only has two
type arguments (|`t| and |`t list|) contrast to |GMap| which had
three. To allow generic functions with a variety of arguments, several
variants of the |FoldMeta| are defined; F\# allows types with the same
name and different number of type arguments to coexist in the same
namespace.

%% Three overloads for the |Sum| constructor are required but only two of
%% them (which are identical) do recursion. This is because values of
%% type |Sum| where the first argument is different to |`t| are
%% representations of internal values of |`t|. For example, the |Company|
%% type introduced above contains sums of type |Sum<<Company<< _
%% >>,_,_>>| and |Sum<<Department<< _ >>,_,_ >>| among other sums. When
%% uniplate is called with |`t| instantiated to |Company|, only the sums
%% of type |Company| should be recursively traversed.  \wouter{While this
%%   is true, I think it's a confusing optimization to present at this
%%   point. I'd argue for having a single definition for Sum, but in the
%%   discussion mentioning that keeping track of the additional type
%%   argument allows us to do more clever optimizations}

The second generic function we define is |Instantiate|, that
reconstructs the value of an algebraic datatype when passed the list
of child nodes. We will store this list in a local, mutable variable
|value|, to which each of the instance definitions below may refer.
\begin{code}

type Instantiate<<vart>>(values` : vart list) =
  inherit FoldMeta<<vart,Meta>>()
  let mutable values = values`

  let pop () = match values with
                | x::xs -> values <- xs;Some x
                | [] -> None

...
\end{code}
To complete this definition, we need to define suitable instances for
the sub-classes of |Meta|. The most interesting case is that for the
|Id| type constructor:
\begin{code}
  override self.FoldMeta(i : Id<<vart>>) =
    match pop () with
    | Some x -> Id x
    | None -> failwith "Not enough args"
    :> Meta
\end{code}
To produce the desired child, we |pop| it off the mutable list of
children we have at our disposal. If no such child exists, we fail
dynamically.

The case of sums and products are analogous to the |Collect| function
in the sense that they do recursion in exactly the same way but return
the generated representation instead of a list.
\begin{code}
  override self.FoldMeta<<`ty>>(
    p: Prod<<`ty,Meta,Meta>>) =
    Prod(self.FoldMeta p.E1,self.FoldMeta p.E2) 
    :> Meta
\end{code}
\begin{code}
  member self.FoldMeta<<`ty>>(
    s : Sum<<`ty,Meta,Meta>>) =
    match s with
    | L m -> Sum<<`ty,Meta,Meta>>(
      self.FoldMeta m |> Choice1Of2)
    | R m -> Sum<<`ty,Meta,Meta>>(
      self.FoldMeta m |> Choice2Of2)
    :> Meta
\end{code}
Finally, the cases for the type constructors |U| and |K| are trivial,
as they do not need to modify the list of |values|.
\begin{code}  
  override self.FoldMeta<<`ty>>(u : U<<`ty>>) = 
    u :> Meta

  override self.FoldMeta<<`ty,`a>>(k : K<<`ty,`a>>) = 
    k :> Meta
\end{code}

The |uniplate| function simply wraps both these results together and
handles the conversions to our type representation:
\begin{code}
let uniplate<<vart>> (x : vart) =
  let g = Generic<<vart>>()
  let rep = g.To x
  let xs = rep |> Collect().FoldMeta
  let inst xs = 
    xs |> Instantiate<<vart>>(xs').FoldMeta<<vart>>
    |> g.From
  (xs, inst)
\end{code}

\section{Limitations of the |FoldMeta| class}
\label{sec:better-meta}
A major limitation of the current implementation is that all the
overloads of |FoldMeta| must return a value of the same type. More
advanced libraries for datatype generic programming use some limited
form of dependent types, possibly through type classes or type
families, to enable generic functions to return types of different
values. The |FoldMeta| class lacks such mechanism as it can be used to
subvert the F\# type system. Consider the following example:
\begin{code}
member self.FoldMeta<<`ty>>(
  v : K<<`ty,Employee>>) = 
  K(v.Elem) :> Meta
\end{code}
The type checker would not object to changing the
function as follows:
\begin{code}
member self.FoldMeta<<`ty>>(
  v : K<<`ty,Employee>>) = 
  K("I am not an Employee!!") :> Meta
\end{code}
This changes the type of value stored in the |K| constructor. This is
type correct since any instance of |K| is a sub-type of |Meta|. If this
result was used by the |From| function of the |Generic| class it would
produce a runtime error.

Such errors could be prevented by revisiting the previous definition
of the |FoldMeta| class, adding an additional type parameters for each
overload:
\begin{code}
type FoldMeta<<
  vart,  -- Generic\ type
  `m,    -- Return\ type\ of\ the\ Meta\ overload
  `s,    -- Return\ type\ of\ the\ Sum\ overload
  `p,    -- Return\ type\ of\ the\ Prod\ overload
  `i,    -- Return\ type\ of\ the\ Id\ overload
  `k,    -- Return\ type\ of\ the\ K\ overload
  `u,    -- Return\ type\ of\ the\ U\ overload
  >>
\end{code}
However, to perform recursive calls, all overloads invoke the overload
for type |Meta| which dispatches the appropriate overload as discussed
in section \ref{sec:foldmeta}. Since the current implementation
requires all the overloads to have the same type, the method must not
check that the return type of the overload it selects is correct. If
additional return types are introduced, this will no longer be the
case. The dispatch could fail at runtime if the selected overload
returns a different type. The problem can be solved by enforcing that
all overloads return values which are a sub-type of some other type,
in this case |`m|, so the dispatcher can safely cast the result to
this type. This can be enforced with additional type constraints:
\begin{code}
type FoldMeta<<
  -- [...]
  when `s :> `m
  and `p :> `m
  and `i :> `m
  and `k :> `m
  and `u :> `m
  >>
\end{code}
Unfortunately, type constraints in F\# can only be used to enforce
that a type must be a sub-class of a \emph{concrete} type, not a type
variable. One alternative is to make the sub-typing relation explicit
with the help of member constraints \footnote{The reader might consider using interfaces but the problem with them is that a type can only implement an interface once \cite{InterfaceLims}.}:
\begin{code}
type FoldMeta<<
  -- [...]
  when `s : (member Cast : unit -> `m)
  and `p : (member Cast : unit -> `m)
  and `i : (member Cast : unit -> `m)
  and `k : (member Cast : unit -> `m)
  and `u : (member Cast : unit -> `m)
  >>
\end{code}
A member constraint imposes the requirement that a member function of
the specified type to be present in the type being instantiated by a
variable. This way the dispatcher |FoldMeta| member can safely cast
the result into type |`m| by calling the |Cast| method of the type
which is required to be present.

%% Readers familiar with F\# might also consider type providers as an
%% alternative approach to the meta-programming required to generate
%% these types. However, type providers cannot accept types as static
%% arguments and the provided types have many restrictions (such as
%% forbidding generic methods) which makes them inapropiate.

\wouter{What about defining a 'real' generic gmap function?}
\wouter{Explicit sub-typing by manual casts}
\ernesto{I don't understand what you mean here}
\section{Discussion}
\wouter{I think we need to make the following points:
  \begin{itemize}
  \item limited type safety when defining generic functions;
  \item type safe calling of generic functions;
  \item automated EP pairs using .NET reflection.
  \item limited possibility to generate generic types (like read) for
    now.
  \end{itemize}
} 
This library was created to study the usability of datatype generic
programming in F\#. In doing so, the existing approaches had to be
adapted to suit F\#'s type system. Also, through the implementing of
this library, the authors have uncovered pieces that have room for
improvement. This section discusses what was learned form the process
and what will be done for the next release of the library.

First of all, due to the use of reflection, the representation types
had to be defined as classes instead of algebraic data types as
typically done in other libraries. This allowed the conversion of a
type-class constraint, as used by Regular, to a sub-type
constraint. However, due to the innate design of the OO-paradigm, a
sub-type constraint ``abstracts away'' the universal quantification
that allows Haskell to select a different overload of a function based
on the instantiation of type variables at the application site of a
function. This mechanism had to be replaced with reflection and is
implemented in the |FoldMeta| class. Although this incurs a runtime
penalty, at the long run, it can be eliminated with a cache.

The library allows a family of generic functions to be defined.  This
is evidenced by defining the |uniplate| function which has been shown
to be a very useful combinator for generic programming. Compared to
reflection, the definition of |uniplate| with our library is much
simpler, less error prone and can be automatically optimized by adding
a cache of function calls. Even though reflection is much more
powerful, the programmer will benefit by using this library in cases
where it is expressive enough for the desired task.

As a consequence of sub-typing, it is no longer possible to statically
check that representations generated by user code are faithful to what
they should be (discussed in section \ref{sec:better-meta}). In
Haskell, this is not a problem. Type variables are universally
quantified (instead of just constrained to |Meta|) so the code is not
allowed to change the structure of the value it receives for
universally quantified types. The paper ``Theorems for
Free''~\cite{Wadler89theoremsfor} illustrates this property in
depth. However, the present library allows any arbitrary
representation to be casted to the type |Meta|. It is possible that
type safety can be improved here by defining |Meta| as an interface
and forcing the overloads of |FoldMeta| to universally quantify over
variables constrained to the |Meta| interface. Nevertheless, it is not
clear how much value this would interfaces bring or whether the
library will remain useful. A major consequence of this limitation is
that producer generic functions, like |read|, are difficult to
type-check for correctness.

To partially address the sub-typing related problems, an extension of
the |Meta| class, which requires sub-typing to be made explicit, is
presented. With this class, each generic overload can specify a
different return type from the remaining overloads. Even though the
approach does not eliminate the problem, it certainly reduces the
situations where things can go wrong. The consequence is that the user
has to provide a much bigger specification for the generic functions
since that variant of the |FoldMeta| class contains one type variable
per overload. It is also necessary to make the sub-typing relation
explicit by defining a |Cast| method.

The examples presented in this paper contain some overhead. The most
notorious one is the |GMap| function. When the argument maps over
ADTs, conversion has to be done several times to apply the
function. There is one potential improvement that will be tested in
the upcoming months to amend this problem. It consists of taking
advantage of the OO-approach and overloading the constructors for
representation types such that they can take values of the represented
type as arguments (like the |Id| constructor). Then when properties of
the constructor are requested (like the |Elem| property of |Sum|), the
input type will be deconstructed on demand instead of doing it eagerly
by the |To| function of the |Generic| class. However, in the ADT case
of |GMap|, the constructors could also have a property that directly
returns the type used to build that representation. This would no
longer have the cost of \emph{de-serializing} the representation. Then
once the mapping is applied, a new representation can be constructed
without having to \emph{serialize} a value. This could bring
significant performance improvements which are only possible thanks to
the OO-approach -- an advantage over Regular or similar libraries.

There are alternatives to datatype generic programming in the F\#
language. Type providers\cite{export:173076} can generate code during
compilation time by executing arbitrary .NET code. They are very
useful to provide typed access to external data sources along with
strongly typed functions to interact with such data. However, they are
not a suitable alternative to datatype generic programming since they
are very restrictive on the type information they can access and the
types they can generate. Another meta-programming tool of F\# is
quotations \cite{export:147193}. They are a library that provides
constructs to generate F\# programs at run-time. Even though every
generic function of this library can be implemented as a quotation
generator for the input type, quotations don't give any improvements
over reflection when it comes to inspecting and traversing a
type. They can be used in a complementary way this library for easier
generation of F\# code at runtime.

\subsection*{Conclusions}

In the report~\cite{CompGen} presents several guidelines are to judge
generic libraries. From the libraries discussed in the paper, this
library would be most similar to Lightweight Implementation of
Generics and Dynamics~\cite{Cheney02alightweight} or
RepLib~\cite{RepLib}; but with a reduced universe. However, it is
worth pointing out a significant advantage of this library:
extensibility. Since generic functions are implemented as OO-classes
in this library, extending them is trivial. One only needs to inherit
from a generic function and add the custom functionality. Another
thing that can be done by this library is overriding some
functionality (but not all) of a generic function. This is simply done
by inheriting from a generic function and overriding one (or more) of
its methods. In Haskell, datatype generic programming libraries can't
do this unless each instance for each representation type is defined
in a separate module due to overlapping instances. Furthermore, in
this library, all variants of a generic function (including the
function itself) can coexist together in the same namespace.

It is possible to use the ideas from datatype generic programming in
order to provide a more structured alternative to reflection. It is
still an open discussion to determine which api would be the best in
order to bring the ideas to languages like F\#. In order to make
datatype generic programming possible in F\#, ideas had to be adapted
to suit F\#'s type system and tools. The use of sub-typing could have
performance benefits since values could be encoded as representations
in such a way that the encoding/decoding only occurs if necessary. One
might argue that Haskell's laziness already does this, but in the case
of the |GMap| function, Haskell would still need to translate a
representation to a value to apply the mapping and convert the result
back to a representation; else the program won't type-check. However,
there were consequences when adapting the library. The most notable
one is that casting can be used to produce representations that are no
longer faithful to the type they intend to represent. This will result
in runtime errors. Fortunately, the richness of the type information
provided by .NET at runtime and the debugging tooling of F\#/.NET make
this problem easier to correct.

%% Datatype generic programming is a well tested solid approach to write
%% generic algorithms. It offers a lot of expressiveness compared to
%% combinator based libraries but has the cost of being harder to use and
%% requiring powerful type systems. The approach has been tested and
%% implemented in F\#. Although safety had to be compromised due to the
%% absense of type system infrastructure in F\#, a useful tool could
%% still be produced. Even though not completely safe, it is more type
%% safe than reflection since only a minimal part of the algorithms
%% require unchecked (or dynamically checked) type operations. In
%% practice, it is much more pleasant having theese unsafe runtime
%% operations in F\# than in languages like Haskell or Scala because the
%% .Net runtime can provide rich information about how/when/why the
%% operation failed. This would result in a segmentation fault in Haskell
%% or a stacktrace with erased types in Scala.

%% The library is on its first release so no optimizations have been done
%% (since a stable api is desired first) but it is clear that DGP opens
%% doors for automated caching of operations which would need to be done
%% manually with reflection. In particular, the approach is referentially
%% transparent when it comes to the type of the arguments. In other
%% words, the same overload will be selected when the arguments given to
%% the method selector have the same type.  This means reflection only
%% needs to be used once to select the method and next time a call with
%% the same types is done, the right method can automatically be
%% dispatched. \todo{Is this clear or should I rather give an example
%%   about how this works?}

%% Compared to existing DGP libraries, the lack of type system
%% infrastructure makes it very inconvenient to write a class of generic
%% functions. Theese are the functions that produce values out of
%% data. The best example is the \verb+read+ function from Haskell. The
%% problem is that as the funciton parses the string, it must generate a
%% representation. But in this library, all type representations are a
%% subclass of \verb+Meta+ so it is hard to statically check that the
%% algorithm is correct. A possible way to address the problem is having
%% a type provider that can be given a type and it produces a new type
%% that is the exact type for the representation. Then the \verb+read+ or
%% any other function must produce a representation with that same type
%% (instead of only a sub-type of \verb+Meta+) and would be reasonable
%% for the F\# compiler to check the correctness of the
%% algorithm. Unfortunately, type providers can't accept types as static
%% arguments.  of the algorithm. \ernesto{This last statement is still
%%   relevant in spite of no longer using type providers}

% \subsection*{Conclusions}

%% We have presented a library for datatype generic programming,
%% implemented in F\#. In spite of the lack of higher-order kinds, it was
%% still possible to reclaim some of the functionality using reflection,
%% abstract classes, and subtyping to provide some static guarantees. The
%% resulting library can be used to define various generic functions
%% familiar from Haskell libraries such as Uniplate and Regular.

% Datatype generic programming was successfully implemented for the F\#
% programming languages. In spite of the absecne of higher-rank
% polymorphism, it was still possible to reclaim some of the
% functionality using reflection and abstract classes to enforce certain
% static assurances. The result is a library wich can define various
% generic functions.

% The main advantage of this approach compared to ordinary reflection is
% type safety. Even though the implementation performs many unsafe
% dynamic type checks, they are masked behind a type-safe interface. It
% is not possible that a generic method is invoked with a representation
% of a type that is not supported by the method. Another minor advantage
% of this approach is providing a structured way to specify how the
% generic methods should be selected through reflection. This opens
% opportunities for automatic optimization since reflection only needs
% to be used once and the method selection can be cached automatically.

% The main disatvantage of this library compared to other DTG libraries
% is the reduced type safety of the approach.  That has practical
% disatvantages which make it hard to define generic functions similar
% to |read|. Although a type error cannot occur when invoking generic
% methods and obtaining the result, the user can still experience
% unexpected behavior if he defines a generic function with the wrong
% type. This type error will simply be ignored by the compiler and the
% selector and resulting in the wrong overload of |FoldMeta| being
% selected by the selector.

%% Compared to reflection, this approach is much less general. In the
%% context of F\#, mutually recursive types are still not supported. The
%% reason is that the |Id| constructor would require an additional type
%% argument for every extra type in the recursion. Advanced DGP libraries
%% using advanced type systems have solved the problem in various ways
%% \cite{multirec}. Generally, the idea consists of using type level
%% functions to define types that can be used as indexes for other
%% types. Then each type of the mutual recursion can be assigned an
%% index. If type providers in F\# could produce generic types, it might
%% be possible to lazyly construct the types required for every type
%% present in a mutual recurison. Another advantage of reflection is that
%% it can be used with any .NET type. This library only works for
%% algebraic datatypes.


%  The approach has been adapted for other languages
% like Scala\cite{scala-jfp}, but it relies heavily on advanced type
% system features. In this paper we will try implementing a simpler
% variant of the approach suitable for simpler languages. In this paper,
% the F\# language is used because it adopted .NET's type system which
% is shared by a family of languages. The present paper is structured in
% the following way:



\todo{Fix overfull hboxes}
\todo{Extend bibliograhpy}

%\acks
% We would like to thank Ruud Koot and the computer science reading club for their

% Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.
\bibliographystyle{abbrvnat}
\bibliography{references}


\end{document}

% Subtyping rather than sub-typing
% datatype vs data type
% avoid the passive voice

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lhs2pdf"
%%% End: 



\documentclass[authoryear,10pt]{sigplanconf}

%lhs2TeX imports -- don't remove!
%include polycode.fmt
%include fsharp.fmt


%% Preamble

\usepackage{amsmath}
\usepackage{listings}
\usepackage{caption}
\usepackage{subcaption}
\usepackage{multirow}
\usepackage{xcolor}
\usepackage{verbatim}
\DeclareCaptionType{copyrightbox}
\usepackage[most]{tcolorbox}

%% TODO notes
% \usepackage{color}
\usepackage{ifthen}
\newboolean{showNotes}
\newboolean{marginNotes}
\setboolean{showNotes}{false}
\setboolean{marginNotes}{true}
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

\newenvironment{fsharp}
  {
    \tcbset{
      frame code={}
      center title,
      left=0pt,
      right=0pt,
      top=0pt,
      bottom=0pt,
      colback=gray!10,
      colframe=white,
      width=8.5cm,
      enlarge left by=0mm,
      boxsep=0pt,
      arc=0pt,outer arc=0pt,
    }
    \begin{tcolorbox}
      %\textsc\bgroup
      % \begin{flushright} {\scriptsize F\#} \end{flushright}
  }
  {
    \end{tcolorbox}

  }

\newenvironment{hask}
  {
    \tcbset{
      frame code={}
      center title,
      left=0pt,
      right=0pt,
      top=0pt,
      bottom=0pt,
      colback=yellow!20,
      colframe=white,
      width=8.5cm,
      enlarge left by=0mm,
      boxsep=0pt,
      arc=0pt,outer arc=0pt,
    }
    \begin{tcolorbox}
      %\textsc\bgroup
      % \begin{flushright} {\scriptsize Haskell} \end{flushright}
  }
  {
    \end{tcolorbox}

  }


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
  paper presents a library for datatype generic programming in F\#,
  built on top of the .NET reflection mechanism. The generic functions
  defined using this library can be called by any other language
  running on the .NET platform.
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
used to describe some collection of types. \emph{Generic} functions
are then defined by induction on the elements of the representation
type. Finally, these libraries typically support some form of
conversion between values of algebraic datatypes and their
corresponding representation. This enables users to call generic
functions on custom datatypes, without having to implement the
underlying conversions manually.

Yet this approach has not been as widely adopted in other
languages. In this paper, we will attempt to address this by
implementing a library for data type generic programming in F\#~\cite{export:192596}. More
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

\item The tool typically used in F\# to implement polytipic
  functions~\cite{polyp} generically is reflection. However,
  reflection imposes a lot of programming overhead and is error
  prone. We provide an alternative method to implement polytipic
  functions with less overhead.

\item Finally, we will show how functions from other Haskell
  libraries, such as Uniplate, may be readily implemented using the
  resulting library (Section~\ref{sec:uniplate}).
\end{itemize}

% \todo{Do we want to make the code available from github? If so, this
%   is usually a good place to mention this.}

We hope that porting the ideas from the datatype generic programming
community to F\# will pave the way for the wider adoption of these
ideas in other .NET languages, such as C\#.

\section{Background}
\label{sec:background}
This section introduces the F\# language and the .NET
platform. Inspired by the `Scrap your boilerplate' approach to
datatype generic programming~\cite{SYB}, we will define a company type
and a function called |IncreaseSalary|. The function increases the
salary of every employee in the company. Our example is different
since our library doesn't support mutually recursive data types and we
intend to present all type declarations allowed in F\#.  Along the
way, we will introduce the the syntax and relevant concepts from F\#
and .NET. We will provide an alternative definition of
|IncreaseSalary| using our library for generic programming in the
second half of this paper.

\subsection{The F\# language}
\label{sec:fsharp}
The F\#~\cite{export:192596} programming language is a functional
language of the ML family. It aims to combine the advantages of
functional programming and Microsoft's .NET platform. To do so, the
F\# designers have adopted numerous features from languages such as
Haskell or OCaml, without sacrificing the ability to interface well
with other .NET languages.  As a result, the language has a much
simpler type system than the type system of Haskell, OCaml or Scala.
F\# performs no type erasure when compiled to the .NET platform.

Before we can define the |IncreaseSalary| function, we will define the
types on which it operates:

\begin{fsharp}\begin{code}
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
\end{code}\end{fsharp}
\begin{fsharp}\begin{code}
      and  set(value) = salary <- value
    override self.NetSalary 
      with get() = self.Salary / 1.12
  end
\end{code}\end{fsharp}
This example demonstrates the different type declarations that F\#
supports.  Besides records, such as |Metadata|, F\# supports algebraic
datatypes (ADTs) that should be familiar to functional
programmers. For example, |Company|, |Department| and |Staff| are
ADTs. Furthermore, programmers in F\# may define classes, such as
|Employee| and |GuatemalanEmployee|. There are several important
differences between classes and datatypes. Records and datatypes may
be deconstructed through pattern matching and are immutable. In
contrast to classes, there is no possible subtyping relation between
datatypes. In .NET terminology, they are \emph{sealed}. Classes in
F\#, on the other hand, behave just as in any other object oriented
language. They can inherit from other classes -- in our example the
class |GuatemalanEmployee| inherits from the |Employee| class. Both
ADTs and classes may contain member functions (or methods) declared
with the |member| keyword. Member functions always take the object on
which they are invoked as an argument, as witnessed by the |self|
identifier before a member function's definition.

These data declarations also use polymorphic types and type
constraints. Polymorphic types define datatypes parametrized by a type
argument.  In this case |Company|, |Department| and
|Staff| accept a single type as argument. In our example, the
type arguments have a type constraint, stating that they must be a
subtype of the |Employee| class. The type constraints are
declared using the |when| keyword.

It is worth pointing out that type arguments can only be of kind
|*|. This is a particularly important limitation in the context of
datatype generic programming since many Haskell libraries rely on
higher kinds.

Next, we implement the |IncreaseSalary| function. To do so, we will
begin by defining an auxiliary function called |UpdateEmployee| that
applies its argument function to every |Employee| of the company:

\begin{fsharp}\begin{code}
type generic(Staff)(t) with
  member self.UpdateEmployee(f) = 
    match self.with
    | Empty -> Empty
    | Member (m,s) -> 
      Member (f m,s.UpdateEmployee f)
type generic(Department)(t) with
  member self.UpdateEmployee(f) =
    match self.with
    | Tech of meta,staff -> 
\end{code}\end{fsharp}
\begin{fsharp}\begin{code}
        Tech (meta,staff.UpdateEmployee f)
    | HR of meta,staff -> 
        HR (meta,staff.UpdateEmployee f)

type generic(Company)(t) with
  member self.UpdateEmployee(f) =
    match self.with
    | Empty -> Empty
    | Member d,c -> 
        Member(
          d.UpdateEmployee f, 
          c.UpdateEmployee f)
\end{code}\end{fsharp}
Here we have chosen to \emph{overload} the |UpdateEmployee| function,
allowing a function with the same name to be defined for different
types. To overload functions in F\#, they must be defined as a member
function. Member functions may be defined post-hoc, i.e., after the
type has been defined.

Using |UpdateEmployee|,  the |IncreaseSalary| function can be defined as follows:
\begin{fsharp}\begin{code}
type generic(Company)(t) with
  member self.IncreaseSalary(v) =
    self.UpdateEmpolyee (
      fun e -> e.Salary <- e.Salary + v;e)
\end{code}\end{fsharp}
Note that because we have defined the |Employee| type as a class, it
is passed by reference in the |UpdateEmployee| function. The argument
function we pass to |UpdateEmployee| mutates the object's |Salary|
property directly and subsequently returns the argument object.

In the later sections we will show how the |UpdateEmployee| function
may also be defined in terms of a generic map, implemented with our
library.  Before doing so, we will give a brief overview of some of
the relevant features of the .NET platform.

\subsection{The .NET platform}
The .NET platform is a common runtime environment supporting a family
of languages. It provides languages with a type system that includes
support for generics and reflection. Many operations on types in F\#,
such as casting, are handled by the .NET platform.

\paragraph{Subtyping}

The .NET platform defines a subtyping relation which is the one used
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
casts. Dynamically checked casts are usually necessary when using
reflection. If a dynamically checked cast fails, an exception is
thrown.

As in most object oriented languages, the .NET subtyping mechanism
allows values to be cast implicitly to any super-type.  The F\#
language uses the keyword |inherit| to denote that a type inherits
from another type.  The subtyping relation does not extend
automatically to polymorphic types: that is, the implication $\tau_a \prec
\tau_b\ \Rightarrow\ \mathtt{T}\langle\tau_a\rangle \; \prec \;
\mathtt{T}\langle\tau_b\rangle$ does not hold in general.

\paragraph{Reflection}

To handle all type operations and collect type information, the .NET
platform defines the abstract class |Type|. Instances of the class
|Type| encode all the type information about values. When F\# is
compiled to the .NET intermediate language, CIL, an instance of the
|Type| class is generated for every type defined in the F\# code. The
.NET platform makes this type information available at runtime. Every
object has the method |GetType| which returns the value of type
|Type|.

The |Type| class is not sealed. Languages can extend it with any
information they want. This allows F\# to include specific metadata
about algebraic datatypes and other F\# specific types in the |Type|
class.  We can use this metadata to query the constructors of an
algebraic datatype, or even to pattern match values with its type
constructors. It is also possible to use reflection to invoke the type
constructors of an ADT to create values of that type. Using reflection
is not type-safe in general since the information gained through
reflection is only available at run-time. Any errors will cause a
runtime exception. Nevertheless, reflection is actively used in
libraries such as FsPickler~\cite{FsPickler}, a general purpose .NET
serializer, and Nancy~\cite{Nancy}, a .NET web framework.

Code written using reflection is usually cluttered with method calls
that execute .NET internal routines but have no relevance in the logic
of the algorithm they implement. This makes it very inconvenient to
use in ordinary code. It also leads to code that is hard to maintain
since its use requires good understanding of .NET's internals.

\section{Type Representations in F\#}
\label{sec:representation}

\begin{figure*}
\centering
\tcbset{
      frame code={}
      center title,
      left=0pt,
      right=0pt,
      top=0pt,
      bottom=0pt,
      colback=gray!10,
      colframe=white,
      width=18cm,
      enlarge left by=0mm,
      boxsep=0pt,
      arc=0pt,outer arc=0pt,
    }
\begin{tcolorbox}
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
type Id<<`ty>>(elem:`ty) =
  class
    inherit Meta()
    self.Elem 
      with get() = elem
  end
\end{code}
\begin{code}
type Sum<<`ty,vara,varb
                when vara :> Meta 
                and varb :> Meta>>(
                elem : Choice<<vara,varb>>) =
  class

    inherit Meta()
    member self.Elem 
      with get() = elem
  end
\end{code}
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
\end{tcolorbox}
\caption{Definition in F\# of all the types used to build type representations.}
\label{fig:rep-def}
\end{figure*}

The core of most libraries for datatype generic programming is a
\emph{representation type} or \emph{universe}. It determines the types
that can be represented and how generic functions are defined. We will
adopt the sums-of-products view of algebraic datatypes, as pioneered
by Generic Haskell~\cite{GenericHaskell} and libraries such as
Regular~\cite{Regular}.

The type system of F\# is not as expressive as Haskell's type
system. In particular, all type variables are necessarily of kind |*|;
furthermore, all calls to overloaded methods must be resolved
statically and cannot depend on how type variables are
instantiated. For these reasons, we will need to adapt the Haskell
approach slightly.

We will define an abstract class, |Meta|, that will be used to define
type representations. Its purpose is to impose type constraints on
type variables. These constraints serve as an alternative to typeclass
constraints that are used in Regular. For example, (a slight variation
of) the following instance is defined in the Regular library:

\begin{hask}
\begin{code}
instance (GMap f, GMap g) => 
  GMap (f :*: g) where
    gmap f (x :*: y) = ...
\end{code}\end{hask}
Instead of abstracting over higher-kinded type arguments, we will
abstract over first-order type variables of kind |*|, and constrain
them to be a sub-type of |Meta|.

In the remainder of this section, we will present the concrete
subtypes of the |Meta| class defined in our library. All the
subclasses of the |Meta| class are parametrized by at least one
(phantom) type argument, |`ty|.  This argument will be instantiated to the
type that a value of type |Meta| is used to represent.

The first subclass of |Meta| is |Sum|, that represents the sum of two
types.  Besides the type argument |`ty|, the |Sum| takes two
additional type arguments: |`a| and |`b|. The |Sum| class stores a single
piece of data, namely a value |elem| of type |Choice<<`a,`b>>|.
The |Choice| type in F\# is
analogous to Haskell's |Either| type. It has two constructors:
|Choice1Of2| and |Choice2Of2|. Note that both |vara| and |varb| have
the constraint that |vara| and |varb| are subtypes of the |Meta|
class.

The second subclass of |Meta| is |Prod|, corresponding to the product
of two types. Besides the |`ty| argument, the |Prod| type accepts two
additional type arguments: |vara| and |varb|. Once again, we require
both |vara| and |varb| to be subtypes of the |Meta| class. Besides
products, we will use the class |U :> Meta| to represent the unit type
which takes no extra type arguments.

Next, the subclass |K| of |Meta| is used to represent types not
defined as algebraic datatypes. This can be used to represent primitive
types, such as |int| or |float|. The |K| constructor takes one extra
type argument: |vara|. This argument corresponds to the type of its
content. Since F\# cannot statically constrain a type to be an
algebraic datatype or not, |vara| has no constraints.

Finally, |Id| is the last subclass of |Meta|. This type is used to
represent recursive types. It only takes the |`ty| type argument used
to refer to recursive occurrences of values of the type being
represented.

The definitions of these types are given in Figure~\ref{fig:rep-def}.
These definitions are not complete since the actual implementation
contains extra code used for reflection which is not relevant when
discussing the universe of types that our library can handle.  The
full definition can be found in the source
code~\cite{FSharp-Generics-Repo}.

We conclude this section with an example of our type
representation. Given the following ADT in F\#:
\begin{fsharp}\begin{code}
type Elems = Cons of int*Elems
                   | Val of int
                   | Nil 
\end{code}\end{fsharp}
We can represent this type as a subtype of the |Meta| class as
follows:
\begin{fsharp}\begin{code}
type ElemsRep = 
  Sum<<
    Elems,
    Sum<<
      Elems,
      Prod<<Elems,K<<Elems,int>>,
        Prod<<Id<<Elems>> >>,U<<Elems>> >> >> >>,
      Sum<<
        unit,
        Prod<<K << Elems>>,int >>, U<< Elems>> >> >>,
        U<<Elems>> >> >>,
    U<<Elems>> >> >>
\end{code}\end{fsharp}

This example shows how nested |Sum| types are used to represent the
three type constructors of the |Elems| type. We show how constructors
of different number of arguments are encoded with the |Prod| type. The
recursive occurrence of |Elems| in the |Cons| constructor is
represented by the |Id| type.

There is some overhead in this representation -- we could simplify the
definition a bit by removing spurious unit types. It is important to
emphasize, however, that these definitions will be \emph{generated}
using .NET's reflection mechanism. To keep the generation process as
simple as possible, we have chosen not to optimize the representation
types.

\subsection*{Generating conversion functions}
\label{sec:generic-class}

The representations are used as a universal interface to implement
algorithms that work on a family of types. It is important to perform
the conversion between types and their representations automatically
since that makes the library convenient to use. Haskell libraries
usually use Template Haskell~\cite{Sheard02templatemeta-programming}
to generate these conversions. Some Haskell compilers even have a
built-in mechanism~\cite{GenericDeriving} for these conversions. The
F\# language does not have the same facilities for meta-programming but
we can use .NET's reflection mechanism to achieve similar results.

The |Object| class of .NET has a method called |GetType : unit ->
Type| which returns a value that contains all the information about
the type of the object on which it is invoked. Since |Type| is an
abstract class, every language hosted on the .NET platform is free to
extend the precise information stored in instances of the |Type|
class. This allows the F\# compiler to include metadata that can be
used to query the (type of the) constructors of any algebraic data
type at runtime.

Using this |GetType| member function, we can
obtain type information at runtime which is used to
traverse the |Type| value and generate the necessary conversion
functions. This functionality is implemented by the |Generic<<`t>>|
class with the following members:
\begin{fsharp}\begin{code}
type Generic<<`t>>() =
  member x.To : vart -> Meta
  member x.From : Meta -> vart
\end{code}\end{fsharp}
Note that these conversions are generated \emph{dynamically}, in
contrast to most Haskell approaches to generic
programming. Intermediate results of this conversion can be cached to
reduce the performance penalty.

\section{Generic functions}
\label{sec:generic-functions}

\begin{figure*}
\tcbset{
      frame code={}
      center title,
      left=0pt,
      right=0pt,
      top=0pt,
      bottom=0pt,
      colback=gray!10,
      colframe=white,
      width=10cm,
      enlarge left by=0mm,
      boxsep=0pt,
      arc=0pt,outer arc=0pt,
    }
\begin{centering}
\begin{tcolorbox}
\begin{code}
AbstractClass
type FoldMeta<<`t,varin,`out>>() =

  abstract FoldMeta : Meta * varin -> `out
  abstract FoldMeta<<`ty>> : Sum<<`ty,Meta,Meta>> * varin -> `out
  abstract FoldMeta<<`ty>> : Prod<<`ty,Meta,Meta>> * varin -> `out
  abstract FoldMeta<<`ty,`a>> : K<<`ty,`a>> * varin -> `out
  abstract FoldMeta : Id<<`t>> * varin -> `out
  abstract FoldMeta<<`ty>> : U<<`ty>> * varin -> `out
\end{code}
\end{tcolorbox}
\end{centering}
\caption{Definition of the |Meta| abstract class for 
  generic functions taking one argument.}
\label{fig:def-meta}
\end{figure*}

The purpose of type representations is to provide an interface that
the programmer can use to define generic functions. Once a function is
defined on all the subtypes of the |Meta| class, it can be executed on
any value whose type may be modeled using the |Meta| class.

To illustrate how generic functions may be defined, we will define a
generic map operator, |gmap|. This function accepts as an argument a
function of type $\tau\to\tau$ and applies the function to every value
of type $\tau$ in a ADT. In Regular, a generic function is defined as
a typeclass. In our library, we define |GMap| as a .NET class.  Every
generic function in our library is implemented as a subclass of the
|FoldMeta| class.  This is an abstract class that specifies the
minimal implementation required to define a generic function. Its
definition is given in Figure \ref{fig:def-meta}.

\begin{fsharp}\begin{code}
type GMap<<`t,`x>>() = 
  class 
  inherit FoldMeta<<
    `t,
    `x -> `x,
    Meta>>()
  -- [...] Implementation [...]
  end
\end{code}\end{fsharp}
The |FoldMeta| class is parametrized by three type
arguments: |`t| which is the type on which the generic functions are
invoked, |varin| which is the input type of the function, |`x->`x| in
this case, and |`out| which is the return type of the generic
function, in this case |Meta|. 

The |FoldMeta| class specifies the definitions necessary to compute
some new result from a value of type |Meta|. Roughly speaking, it
requires a method for each concrete subtype of the |Meta| class. Note
that all the methods are universally quantified over the type being
represented, |`ty|.  The only exception is the |Id|, representing
recursive occurrences, that requires a member function of type
|Id<<`t>> * varin -> `out|, where |`t| is the first type argument of
|FoldMeta|.

To illustrate why this distinction is necessary, consider invoking the
|GMap| function on the |Company| type. This type contains values of
type |Department|.  As a result, intermediate |Sum| constructors may
have a type that is of the form |Sum<<Department<< _ >>,_,_ >>| or a
type of the form |Sum<<Company<< _ >>,_,_ >>|. In order to handle both
of these cases, the |`ty| argument of the |Sum| type must be
universally quantified in the corresponding definition of
|FoldMeta|. On the other hand, recursive occurrences always store a
value of the type being represented. Hence the |FoldMeta| definition
for the |Id| type constructor is specialized to |`t| rather than being
polymorphic for any |`ty|. Here we adopt the convention that |`t|
always refers to the type being represented and |`ty| is a universally
quantified type variable corresponding to the specific type of each
method.

By overriding the |FoldMeta| methods in the concrete |GMap| class, we
will define the desired map operation. The |FoldMeta| class and its
member functions will be explained in detail in Section
\ref{sec:foldmeta}; for the moment, we will restrict ourselves to the
methods that we override in the |GMap| class. The first method we
override handles the |Sum| type constructor:
\begin{fsharp}\begin{code}
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
\end{code}\end{fsharp}
This example uses the following F\# specific constructs:
\begin{itemize}
\item the the pipeline operator ($\!\!\!\!$ | ||> | $\!\!\!\!$) which
  is simply reversed function application: |x ||> f = f x|. This is a
  common operator used in F\#, analogous to the (|$|) in Haskell but
  asociates to the left and has its arguments flipped. %$
\item The |override| keyword serves the same purpose as |member| but
  results in a compile time error if no matching |member| is found in
  the super-class.
\end{itemize}

The definition is fairly unremarkable: it pattern matches on its
argument and applies the |FoldMeta| function to the values contained
in the |Sum| type. It then reconstructs a |Sum| instance with the
results of the recursive call. Lastly, it casts the result back to the
type |Meta|. The recursive calls of |FoldMeta| happen through the
member function |FoldMeta : Meta * varin -> `out| of the |FoldMeta|
class. We defer its description to section \ref{sec:foldmeta}.

The next definition handles products:
\begin{fsharp}\begin{code}
override x.FoldMeta<<`ty>>
  (v : Prod<<`ty,Meta,Meta>>
  ,f : `x -> `x) =
    Prod<<Meta,Meta>>(
      x.FoldMeta(v.E1,f),
      x.FoldMeta(v.E2,f))
    :> Meta
\end{code}\end{fsharp}
The type |Prod| contains the properties |E1| and |E2| which store the
two constituent elements of the product. Once again, we recursively
invoke |FoldMeta| on these values, reassemble the result and cast it
back to the type |Meta|. The definition for unit types, |U|, is
similarly unremarkable.

We define two cases to handle the |K| type constructor:
\begin{fsharp}\begin{code}
member x.FoldMeta<<`ty>>(
  v : K<<`ty,`x>>, f : `x->`x) = 
  K(f v.Elem) :> Meta

override x.FoldMeta<<`ty,`a>>(k : K<<`ty,`a>>
                         ,f : `x -> `x) = k :> Meta

\end{code}\end{fsharp}
The first definition defines a new member function. It applies the
function |f| to a value of type |`x|. The property |Elem| of the |K|
constructor returns the value of type |`x|, which we pass to |f|,
before casting the result back to a value of type |Meta|. The second
definition overrides the required |FoldMeta| member function on |K|;
this definition leaves the underlying value untouched.

The case for the |Id| constructor is a bit more involved: 
\begin{fsharp}\begin{code}
override x.FoldMeta(v : Id<<`t>>,f : `x -> `x) =
    let g = Generic<<`t>>()
    Id<<`t>>(x.FoldMeta(
      g.To c.Elem,f) |> g.From)
    :> Meta
\end{code}\end{fsharp}
The |Id| case of the abstract |FoldMeta| member instantiates the |`ty|
argument of the |Id| constructor to |`t|. This means that the |Id|
case only needs to be specified for the type |`t|, the type to which
the generic function is being applied. Contrary to the other
overloads, it is not universally quantified for all types. The |Id|
constructor stores a single value, |Elem|, of type |`t|.  Using the
|Generic<<`ty>>| class it is possible to convert this |`t| to a value
of type |Meta|.  After calling the |FoldMeta| function recursively, we
can convert the result back to the original type.

We have now completed the required definitions for our |GMap| class
but there still remains one problem. We have assumed that all
algebraic data types will be converted to a value of type |Meta|,
after which we may apply overridden methods to obtain the desired
result. Now suppose the \emph{function} we are mapping has the type |X
-> X|, for some algebraic data type |X|. In that case, we do
\emph{not} want to convert values of type |X| to their corresponding
representation (and apply the generic |GMap| function), but rather we
would like to transform these values using the argument function. To
resolve this, we need to provide several additional definitions.

We will define four additional member functions with a more specific
type. Recall that in our declaration of |GMap|, we stated that the
argument |f| has type |`x -> `x|. Each of the new member functions
will specifically work on representations of the type |`x|, that is,
the type of values being transformed using the |GMap| function:
\begin{fsharp}\begin{code}
let mapper (f : `x->`x) (v : Meta) =
  let g = Generic<<`x>>()
  v |> g.From |> f |> g.To
member x.FoldMeta(
  u : U<<`x>>,f : `x->`x) = mapper f u
member x.FoldMeta<<`a>>(
  u : K<<`x,`a>>,f : `x->`x) = mapper f u
member x.FoldMeta(
  p : Prod<<`x,Meta,Meta>>,f : `x->`x) = mapper f p
\end{code}\end{fsharp}
\begin{fsharp}\begin{code}
member x.FoldMeta(
  s : Sum<<`x,Meta,Meta>>,f : `x->`x) = mapper f s
\end{code}\end{fsharp}
All of these member functions behave similarly: they convert the
generic representation back to a value of type |`x|, apply the
function |f|, and convert the result back to its corresponding
representation of type |Meta|.

Now we can use the |GMap :> FoldMeta| class to define the
following |gmap| function:
\begin{fsharp}\begin{code}
member x.gmap(x : vart,f : `x -> `x) =
    let gen = Generic<<`x>>()
    x.FoldMeta(gen.To x,f)
    |> gen.From
\end{code}\end{fsharp}
Calling this function, requires dispatching on the representation
type, which is handled by the |FoldMeta| and its member function. An
instance of |GMap| with | <<`t>> | set to |Company| and | <<`x>> | set
to |Employee| would implement the |UpdateEmployee| function introduced
in section \ref{sec:fsharp}.

\section{The |FoldMeta| class}
\label{sec:foldmeta}

In the previous section, we assumed the existence of a |FoldMeta|
function with type |Meta * (`x->`x) -> Meta|. Before getting into the
details of this function, we would like to revisit the problem that it
needs to solve. Consider the following instances, defining a fragment
of a generic |map| function in Haskell:
\begin{hask}\begin{code}
instance (GMap a,GMap b) => 
  GMap (a :+: b) where
  gmap (L a) f = L (gmap a f)
  gmap (R b) f = R (gmap a f)

instance (GMap (K Int)) where
  gmap (K v) f = K (f v)

instance GMap U where
  gmap U _ = U
\end{code}\end{hask}
Let's take a look at the |GMap| definition for the |:+:| type. This
function makes a recursive call to |gmap| -- but which overload will
get called?  There are three different overloads to choose from.  In
Haskell, a choice is not made until enough type information is
present. The |GMap| function might be invoked with a value of type |U
:+: U|, or a value of type |K Int :+: K Int|, or even |GMap a => a :+:
K Int|.  The chosen overload depends on the types at the \emph{call
  site} and might be different in every call.

We could try adopting a similar approach in F\#, by defining the
following member functions:
\begin{fsharp}\begin{code}

member x.FoldMeta<<`ty,`a,`b>>(
  s : Sum<<`ty,`a,`b>>, f : int -> int) =
  match s.Elem with
  | Choice1Of2 a -> 
    Sum<<`ty,`a,`b>>(
      x.FoldMeta(a,f) |> Choice1Of2)
  | Choice2Of2 b ->
    Sum<<`ty,`a,`b>>(
      x.FoldMeta(b,f) |> Choice1Of2)

member x.FoldMeta<<`ty>>(
  k : K<<`ty,int>>,f : int -> int) = (K (f k.Elem))

member x.FoldMeta<<`ty>>(
  u : U<<`ty>>,f : int -> int) = u
\end{code}\end{fsharp}
However, this code is rejected by the F\# compiler. At the definition
site of the |Sum| case of |FoldMeta|, it is still unclear how to
resolve the recursive calls to specific overloads. The F\# compiler
cannot wait until |FoldMeta| is applied to a value and more type
information is present in order to decide which function to invoke. In
object oriented languages, abstract methods are usually used to
dispatch different methods depending on the argument. This approach
does not work for our purposes because it would require that every
specific instance of a polymporphic type overrides the method
differently. For example, if for the |K| constructor one wanted a
|FoldMeta| specialized for |int| and another polymorphic for all |`t|;
|K<<int>>| and |K<<`t>>| would require a different override of
|FoldMeta|.

We resolved this problem by defining a |FoldMeta| function of type
|Meta*varin -> `out|.  This function can also be invoked with the
internal elements of |Sum| or |Product| constructors since they are
parametrized by variables |`a,`b :> Meta|. This |FoldMeta| function
then selects the corresponding `instance' that should be invoked based
on the type of its argument. Note that this is handled statically in
Haskell, but must necessarily be done dynamically in F\#.

To define the |FoldMeta| function that dispatches based on its
argument's type, we once again use the .NET reflection mechanism. The
|FoldMeta| function inspects the type of its argument. If we have
exactly the right method at our disposal, we invoke that method. We
only instantiate a more generic method when necessary. This ensures
the desired behavior for the two definitions of |GMap| for |K| that
we saw previously, or the use of the |mapper| function to prevent the
unfolding of algebraic data types to their representation.

Note that the definition of a new generic function does not require
any casting or reflection. That functionality is abstracted away by
using a common representation, |Meta|, and a general purpose traversal
of such representations, |FoldMeta|.

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
\begin{fsharp}\begin{code}
type Arith =
  | Op of string*Arith*Arith
  | Neg of Arith
  | Val of int
  
let (c,f) = uniplate (
  Op ("add",Neg (Val 5),Val 8))
-- prints\ [Neg (Val 5);Val 8]
printf "%A" c
-- prints\ Op (``add",Val 1,Val 2)
printf "%A" (f [Val 1;Val 2]) 
\end{code}\end{fsharp}
To define the function, we will define two auxiliary generic
functions. The first is |Collect| which computes the list of
child nodes:
\begin{fsharp}\begin{code}
type Collect<<vart>>() =
  inherit FoldMeta<<vart,vart list>>()

  member self.FoldMeta<<`ty>>(
    c : Sum<<`ty,Meta,Meta>>) =
    match c.Elem with
    | Choice1Of2 m -> self.Collect m
    | Choice2Of2 m -> self.Collect m

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
\end{code}\end{fsharp}
The function is straightforward to understand. Values of the |Sum|
type are processed recursively; the results of products are combined
by concatenating the resulting lists. Constants and unit types return
an empty list. The only interesting case is that for the |Id| type
constructor, which returns a singleton list with its associated
value. Note that the |FoldMeta| class only has two type arguments
(|`t| and |`t list|), in contrast to |GMap| that had three type
arguments. To allow generic functions with a variety of arguments, our
library defines several variations of the |FoldMeta| class. F\# allows
types with the same name and different number of type arguments to
coexist in the same namespace.

The second generic function we define is |Instantiate|, that
reconstructs the value of an algebraic datatype when passed the list
of child nodes. We will store this list in a local, mutable variable
|value|, to which each of the instance definitions below may refer.
\begin{fsharp}\begin{code}

type Instantiate<<vart>>(values` : vart list) =
  inherit FoldMeta<<vart,Meta>>()
  let mutable values = values`

  let pop () = match values with
                | x::xs -> values <- xs;Some x
                | [] -> None

...
\end{code}\end{fsharp}
To complete this definition, we need to define suitable instances for
the subclasses of |Meta|. The most interesting case is that for the
|Id| type constructor:
\begin{fsharp}\begin{code}
  override self.FoldMeta(i : Id<<vart>>) =
    match pop () with
    | Some x -> Id x
    | None -> failwith "Not enough args"
    :> Meta
\end{code}\end{fsharp}
To produce the desired child, we |pop| it off the mutable list of
children we have at our disposal. If such child doesn't exist, the
list we passed is too short and the function fails.

The case of sums and products are analogous to the |Collect| function,
making two recursive calls to construct a new |Meta| value:
\begin{fsharp}\begin{code}
  override self.FoldMeta<<`ty>>(
    p: Prod<<`ty,Meta,Meta>>) =
    Prod(self.FoldMeta p.E1,self.FoldMeta p.E2) 
    :> Meta
  member self.FoldMeta<<`ty>>(
    s : Sum<<`ty,Meta,Meta>>) =
    match s with
    | Choice1Of2 m -> Sum<<`ty,Meta,Meta>>(
      self.FoldMeta m |> Choice1Of2)
    | Choice2Of2 m -> Sum<<`ty,Meta,Meta>>(
\end{code}\end{fsharp}
\begin{fsharp}\begin{code}
      self.FoldMeta m |> Choice2Of2)
    :> Meta
\end{code}\end{fsharp}
Note that these definitions rely on the list of values being mutable
and F\#'s call-by-value semantics. In the case for products, we know
that the first call |self.FoldMeta p.E1| will be evaluated first,
consuming the required child nodes from the list of values, before
evaluation continues with the second component of the tuple.

Finally, the cases for the type constructors |U| and |K| are trivial,
as they do not need to modify the list of |values|.
\begin{fsharp}\begin{code}  
  override self.FoldMeta<<`ty>>(u : U<<`ty>>) = 
    u :> Meta

  override self.FoldMeta<<`ty,`a>>(k : K<<`ty,`a>>) = 
    k :> Meta
\end{code}\end{fsharp}

The |uniplate| function simply wraps both these results together and
handles the conversions to our type representation:
\begin{fsharp}\begin{code}
let uniplate<<vart>> (x : vart) =
  let g = Generic<<vart>>()
  let rep = g.To x
  let xs = rep |> Collect().FoldMeta
  let inst xs = 
    xs |> Instantiate<<vart>>(xs').FoldMeta<<vart>>
    |> g.From
  (xs, inst)
\end{code}\end{fsharp}


\section{Limitations of the |FoldMeta| class}
\label{sec:better-meta}
The |FoldMeta| class intends to provide a generic interface that
abstract away the use of reflection in order to traverse and construct
values of many types generically. It is more restrictive than
Haskell's type system in the class of functions that it can define. A
very obvious example of such restrictions is generic equality since it
requires induction on two values instead of one.

Variants of the |FoldMeta| class that perform induction over more than
one value are possible. It is only necessary that all cases for one
argument are covered to ensure that pattern matching is
exahustive. For example, we can extend |FoldMeta| as:
\begin{fsharp}\begin{code}
AbstractClass
type FoldMeta<<`t,`out>>() =
abstract FoldMeta 
  : Meta * Meta -> `out
\end{code}\end{fsharp}
\begin{fsharp}\begin{code}
abstract FoldMeta<<`ty>> 
  : Sum<<`ty,Meta,Meta>> * Meta -> `out
abstract FoldMeta<<`ty>> 
  : Prod<<`ty,Meta,Meta>> * Meta -> `out
abstract FoldMeta<<`ty,`a>> 
  : K<<`ty,`a>> * Meta -> `out
abstract FoldMeta 
  : Id<<`t>> * Meta -> `out
abstract FoldMeta<<`ty>> 
  : U<<`ty>> * Meta -> `out
\end{code}\end{fsharp}
The programmer can then overload any of the methods with specific
instances of the second argument which can then be pattern matched
with reflection. For example, to define generic equality, one would
like to have an overload of the |Sum| case with type:
\begin{fsharp}\begin{code}
member FoldMeta<<`ty>> 
  : Sum<<`ty,Meta,Meta>> * Sum<<`ty,Meta,Meta>> 
  -> `out
\end{code}\end{fsharp}
If |FoldMeta| were invoked with both arguments being |Sum| then this
overload would get called. If the second argument is not |Sum| then the
overload accepting a |Meta| would be invoked. This way it is possible
increase the class of generic functions definable by our library
although Haskell's type system will always be more expressive.

Another limitation of the current implementation is that all the
overloads of |FoldMeta| must return a value of the same type. More
advanced libraries for datatype generic programming use some limited
form of dependent types, possibly through type classes or type
families, to allow generic functions to return values of different
types. The |FoldMeta| class lacks such mechanism as it can be used to
subvert the F\# type system. Consider the following example:
\begin{fsharp}\begin{code}
member self.FoldMeta<<`ty>>(
  v : K<<`ty,Employee>>) = K(v.Elem) :> Meta
\end{code}\end{fsharp}
The type checker would not object to changing the
function as follows:
\begin{fsharp}\begin{code}
member self.FoldMeta<<`ty>>(
  v : K<<`ty,Employee>>) = 
  K("I am not an Employee!!") :> Meta
\end{code}\end{fsharp}
This function now changes the type of the value stored in the |K|
constructor, before casting it to the |Meta| type. This is type
correct since any instance of |K| is a subtype of |Meta|. However, if
the result of this function is passed to the |From| function that
generated the original representation it results in a runtime error.

Such errors could be prevented by revisiting the previous definition
of the |FoldMeta| class and adding additional type parameters for each
required overload.
\begin{fsharp}\begin{code}
type FoldMeta<<
  vart,  -- Generic\ type
  `m,    -- Return\ type\ of\ the\ Meta\ overload
  `s,    -- Return\ type\ of\ the\ Sum\ overload
  `p,    -- Return\ type\ of\ the\ Prod\ overload
  `i,    -- Return\ type\ of\ the\ Id\ overload
  `k,    -- Return\ type\ of\ the\ K\ overload
  `u,    -- Return\ type\ of\ the\ U\ overload
  >>
\end{code}\end{fsharp}
However, to perform recursive calls, all overloaded functions invoke
the overload specialized for the |Meta| type, which dispatches as
discussed in section \ref{sec:foldmeta}. Since the current
implementation requires all the overloaded definitions to have the
same type, the method does not need to check that the return type of
the overload it selects is correct. This would no longer be the case
if different return types are permitted. The dispatch could fail at
runtime if the selected overload returns a different type. The problem
can be solved by enforcing that all overloads return values which are
a subtype of some other type, in this case |`m|, so the dispatcher can
safely cast the result to this type. This can be enforced with
additional type constraints:
\begin{fsharp}\begin{code}
type FoldMeta<<
  -- [...]
  when `s :> `m
  and `p :> `m
  and `i :> `m
  and `k :> `m
  and `u :> `m
  >>
\end{code}\end{fsharp}
Unfortunately, type constraints in F\# can only be used to enforce
that a type must be a subclass of a \emph{concrete} type, not a type
variable. One alternative is to make the subtyping relation explicit
with the help of member constraints :
\begin{fsharp}\begin{code}
type FoldMeta<<
  -- [...]
  when `s : (member Cast : unit -> `m)
  and `p : (member Cast : unit -> `m)
  and `i : (member Cast : unit -> `m)
  and `k : (member Cast : unit -> `m)
\end{code}\end{fsharp}
\begin{fsharp}\begin{code}
  and `u : (member Cast : unit -> `m)
  >>
\end{code}\end{fsharp}
A member constraint imposes the requirement that a member function of
the specified type is present in the type that instantiates the
variable. This way the dispatcher |FoldMeta| member can safely cast
the result into type |`m| by calling the |Cast| method of the given
value. Although this approach may work in principle, it highlights
some of the limitations of F\# that we have encountered.

There are a few cases where our usage subtyping and the |FoldMeta|
class has certain advantages compared to many Haskell
libraries. Suppose we want to define an alternative version of the
|GMap| function, |ShallowGMap|, that does not traverse recursive
occurrences of its argument. Essentially, these two definitions are
the same -- the only difference is in the |Id| case. Using the F\#
approach we have described, we can define a new subclass of |GMap|,
overriding the instance for |Id|:
\begin{fsharp}\begin{code}
type ShallowGMap<<`t,`x>>() =
  inherit GMap<<`t,`x>>()
 
  override self.FoldMeta(i : Id<<`t>>,f : `x -> `x) = i
\end{code}\end{fsharp}
This is harder to do in most Haskell libraries. Generic functions
defined using type classes, such as those in the Regular library, make
it very hard to re-use existing instance definitions in new generic
functions. The class and module system of F\#, on the other hand, make
it fairly straightforward to define different variations of the same
function in the same namespace.

\section{Discussion}

This paper aims to explore the possibility of using of datatype
generic programming in F\#. To do so, we had to adapt the existing
approaches to better match F\#'s type system. We also substituted some
type level computations performed by the Haskell compiler with
reflection. In the remainder of this section, we will reflect about
our library and the limitations of F\#.

First of all, due to the use of reflection, our representation types
are defined as classes, instead of (generalized) algebraic data types
or type classes as typically done in most Haskell libraries. As a
result, type-class constraints, as used by Regular, were translated to
subtype constraints in F\#. Due to the limitations of F\#, we manually
implemented part of the type-directed dispatch of Haskell's type
classes in our own |FoldMeta| class. As a result, we need to do more
work at runtime, even if memoizing results can help improve
performance.

The library makes it possible to define a wide variety of generic
functions. Our implementation of the |uniplate| method highlights that
new generic functions can be added without having to use any .NET
reflection. The expresiveness of the library is limited by the fact
that the programmer must use the |FoldMeta| class as the interface to
define generic functions. This is done to ensure complete
definitions. It is possible to provide variants of |FoldMeta| to
increase expressiveness but this will clutter the library with
definitions and its expressiveness will never be on par to that of
Regular. An alternative would be to allow the programmer to provide
its own definitions of the |FoldMeta| class. This could be achieved by
requiring that the programmer annotates the definition with as special
pragma. Then the compiled F\# assemblies can be checked
post-compilation for consistency using reflection since all the type
information is still present after compilation and the compiled
assemblies can be dynamically loaded. This technique is used by
Websharper~\cite{websharper} to compile F\# into Javascript.


%% Although reflection is a very powerful
%% programming technique, there is ample opportunity for programmers to
%% make mistakes. We hope that the generic functions defined using our
%% library may be a bit safer.

One of the advantages of using representations to define generic
functions is the ability to construct values generically. Although our
library allows it, it is much less convenient than using Haskell since
our use of subtyping and casting values to the |Meta| class might
result in unsafe \emph{generic} functions.  That is, a type-correct
generic function may return a result that throws an exception once it
is converted back to an algebraic data type. We already saw this in
the definition of |GMap| -- it was certainly possible to produce
ill-formed representation types and cast the result back to the |Meta|
type. The same problems can also occur when defining other generic
functions, such as |read|, that need to produce a representation of
type |Meta|. The F\# type system will not object to definitions that
produce the wrong kind of representation. It might be possible to
increase safety by implementing additional checks using reflection and
this is left as future research.

There are alternative mechanisms that could be used for datatype
generic programming in F\#. Type providers~\cite{export:173076} can be
used to generate types at compilation time by executing arbitrary .NET
code. They are typically used to provide typed access to external data
sources, such as a database. Although we have experimented with using
type providers to generate representation types, we abandoned this
approach. Type providers have several severe restrictions on the type
information they can access and the types they can
generate. Alternatively, the \emph{quotations}
library~\cite{export:147193} provides constructs to generate F\#
programs at run-time. Even though some functions can be implemented
generically by using quotations, the approach has no convenient way to
pattern match values generically.

Datatype generic programming has been attempted in other object
oriented languages such as Scala~\cite{scala-jfp}. This library makes
makes use of higher-kinds and traits to define representations and
generic functions are defined by cases in a similar fashion as in
Regular. The library uses implicit parameters instead of reflection
for method dispatch. Type representations must be specified manually
but the compiler can typecheck the correctness of the definition. The
approach also enjoys the extensibility advantages present in our
library.

Polytipic functions are difficult to implement in F\#. Programmers
usually define the same function multiple times or use reflection when
multiple definitions are not feasible. We show that the ideas of
datatype generic programming can be used to implement some polytipic
functions in a simpler way. We use reflection to implement the library
and show that .NET's implementation of reflection is very robust and
can be used to achieve good results -- especially since compiled code
can be dynamically loaded in a post compilation stage. However, work
typically done by the type system of Haskell must be implemented
manually via reflection; yet the user of the library does not need to
know about the implementation.

The idea of datatype generic programming is now almost twenty years
old~\cite{polyp, backhouse}. Yet the approach has not been widely
adopted outside of the functional programming community, despite
several attempts to implement libraries in languages such as
Scala~\cite{scala-jfp}. We believe that there is still much work to be
done to transfer expertise from the datatype generic programming
community to other, more mainstream programming languages. We hope
that the library we have presented here is another small step down
that road.


% It is possible to use the ideas of datatype generic programming to
% provided a more structured alternative to reflection. It is still an
% open discussion determining what the best interface is given the type
% system limitations in F\#. This paper presents an initial approach
% inspired from the lightweight library Regular.

% The primary advantage of F\# over Haskell is that modules and classes
% make it very easy to re-use code and customize existing generic
% functions with new functionality.

% The main limitation was F\#'s type system. To accommodate, a custom
% method dispatch mechanism was implemented using reflection. This
% method imitates what the Haskell compiler performs during compilation
% to select function overloads. The absence of higher kinds also make it
% difficult to properly constrain the type of generic functions. In
% section \ref{sec:better-meta}, we present some options to mitigate the
% problem although it is impossible reach the expressiveness of higher
% kinds with the approach. At this moment it is very unlikely that F\#
% will ever support generics with higher kinds. We hope that this
% library serves as motivation to include higher kinds in F\#.




%% In the report~\cite{CompGen} presents several guidelines are to judge
%% generic libraries. From the libraries discussed in the paper, this
%% library would be most similar to Lightweight Implementation of
%% Generics and Dynamics~\cite{Cheney02alightweight} or
%% RepLib~\cite{RepLib}; but with a reduced universe. However, it is
%% worth pointing out a significant advantage of this library:
%% extensibility. Since generic functions are implemented as OO-classes
%% in this library, extending them is trivial. One only needs to inherit
%% from a generic function and add the custom functionality. It is also
%% possible to override the functionality of some parts (but not all) of
%% a generic function. This is simply done by inheriting from a generic
%% function and overriding one (or more) of its methods. In Haskell,
%% datatype generic programming libraries can't do this unless each
%% instance for each representation type is defined in a separate module
%% due to overlapping instances. Furthermore, in this library, all
%% variants of a generic function (including the function itself) can
%% coexist together in the same namespace.

%% It is possible to use the ideas from datatype generic programming in
%% order to provide a more structured alternative to reflection. It is
%% still an open discussion to determine which api would be the best in
%% order to bring the ideas to languages like F\#. In order to make
%% datatype generic programming possible in F\#, ideas had to be adapted
%% to suit F\#'s type system and tools. The use of subtyping could have
%% performance benefits since values could be encoded as representations
%% in such a way that the encoding/decoding only occurs if necessary. One
%% might argue that Haskell's laziness already does this, but in the case
%% of the |GMap| function, Haskell would still need to translate a
%% representation to a value to apply the mapping and convert the result
%% back to a representation; else the program won't type-check. However,
%% there were consequences when adapting the library. The most notable
%% one is that casting can be used to produce representations that are no
%% longer faithful to the type they intend to represent. This will result
%% in runtime errors. Fortunately, the richness of the type information
%% provided by .NET at runtime and the debugging tooling of F\#/.NET make
%% this problem easier to correct.

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
%% (instead of only a subtype of \verb+Meta+) and would be reasonable
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



\acks We would like to thank the Software Technology Reading Club of
the University of Utrecht for their helpful feedback on a draft
version of this paper.

\bibliographystyle{abbrvnat}
\bibliography{references}


\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lhs2pdf"
%%% End: 



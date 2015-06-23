\documentclass[8pt]{extarticle}

%lhs2TeX imports -- don't remove!
%include polycode.fmt
%include fsharp.fmt

\usepackage{extsizes}
\usepackage{fullpage}
\usepackage{amsmath,amsfonts,amssymb}
\usepackage{cite}
\usepackage{hyperref}
\usepackage{listings}
\usepackage{alltt}
\usepackage{amsmath}
\usepackage{listings}
\usepackage{caption}
\usepackage{subcaption}
\usepackage{multirow}
\usepackage{color}
\usepackage{ifthen}


\newcommand{\todo}[1]{\marginpar{\textcolor{red}{\textbf{Todo:~}#1}}}

\author{Ernesto Rodriguez}
\begin{document}
\Huge{\bf Generic Programming in F\#\\[1cm]}
\large{\bf Ernesto Rodriguez\\[0.5cm]}
\emph{Computer Science \\ Utrecht University \\ Utrecht \\ The Netherlands \\[0.5cm]}
\emph{Type: Master's Thesis Proposal \\ Date: November 28th, 2015 \\ Supervisor: Dr. Wouter Swierstra\\}
\line(1,0){520}\\ \\
\line(1,0){520}

\part{Background}
\section{Datatype Generic Programming}

Functional programming languages often use algebraic data types (ADTs)
in order to represent values. ADTs are defined by cases by providing a
type constructor for each case and the type of values that the
constructor accepts in order to produce a value of the ADT being
defined. In other words, a type constructor is a function that takes a
group of values of different types and produces a value of the type of
the ADT.

To define functions over ADTs, functional languages provide a
mechanism to deconstruct ADTs called pattern matching. This mechanism
allows the programmer to check wether a particular value was
constructed using the specified type constructor and allows the
programmer to extract the arguments used to produce the value. This
mechanism is very elegant since it allows to define functions by
induction, however it has several shortcommings.

A function that pattern matches a value over the constructors of a
particular ADT restricts that the type of the value being pattern
matched to be monomorphic. This leads to functions being implemented
multiple times -- either when a existing ADT is modified or a new ADT
is declared~\cite{polyp}. Since functional programming is all about
abstraction, several methods have been developed to allow functions to
become more polymorphic.

An ADT can be decalred to be higher-kinded. This means that a
definition of a list |data List = Cons Int List palo Nil| can abstract
over its content and become |data List a = Cons a (List a) palo
Nil|. Then a function, such as lenght, might de-construct the list
without performing any operations on its contents -- the type
represented by |a|. Such function can operate on a list of any type --
this is called parametric polymorphism. The programmer might also wish
to implement functions that operate on the contents of a list without
restricting the type of the list's content to be monomorphic. This can
be done by requiring that the function is also provided with a set of
operations that can be performed on its argument. For example, the
|sum| function could be implemented by requiring that a function to
add two elements of type |a| is provided. This is called ad-hoc
polymorphism.

Both of theese approaches can be used to define generic
functions. This is evidenced by the libraries Scrap your Boilerpate
Code~\cite{SYB} and Uniplate~\cite{Uniplate}. Both libraries specify a
family of operations that must be supported by a type and use ad-hoc
polymorphism to implement many generic functions (for example |length|
or |increment|) in terms of the family of operations. The programer
only needs to do pattern matching when defining theese base operations
and both libraries provide mechanisms to do it automatically.

Although both of theese features allow the definition of many generic
functions, a more general approach exists. Recall that every value
expressed as an ADT is a type constructor followed by values of other
types. For simplicity consider type constructors taking only one
argument, they look something like |C a|. One could then define
functions that generalize over \emph{every} type constructor. This is
the idea behind polytipic programming~\cite{polyp} which later evolved
into Datatype Generic Programming.

This method has matured over many years in Haskell alone there are
numerous tools and libraries for datatype generic programming,
including PolyP~\cite{polyp}, Generic Haskell~\cite{GenericHaskell},
RepLib~\cite{RepLib}, Regular~\cite{Regular},
Multi-Rec~\cite{multirec}, Instant Generics~\cite{instant2} and many
others. Some Haskell compilers even support Datatype Generic
Programming natively. The present thesis focuses on Datatype Generic
Programming and will use Regular~\cite{Regular} as a reference.

\subsection{Generic Programming with Regular}

The idea behind Datatype Generic Programming is to encode ADTs using
only a handful of datatypes, such encoding is called a
\emph{representation}. Each library uses different types to define
representations. Representations can encode many ADTs but not all of
them; the ADTs that are expressible by a representation is called the
\emph{universe}.

In the case of Regular, its universe are all the ADTs that:
\begin{itemize}
\item Have no type arguments (are of kind *)
\item Are not mutually recursive
\end{itemize}
This universe includes many common types like lists, trees and simple
DSLs but is smaller than the set of types definible in Haskell 98.

To represent its universe, regular uses the following types:
\begin{code}
data K a r = K a
data Id r = Id r
data Unit r = Unit
data (f oplus g) r = Inl (f r) | Inr (g r)
data (f otimes g) r = f r otimes g r
\end{code}

The types have the following roles:
\begin{itemize}
\item |K| represents the occurence of values of primitive types (eg. |Int| or |Bool|)
\item |Id| represents recursion over the same type
\item |Unit| represents a constructor which takes no arguments
\item |(f oplus g)| represents sum of two representations. This happens when a type has multiple constructors
\item |(f otimes g)| represents product of two representstions. This happens when a constructor takes multiple arguments.
\end{itemize}

To familiarize ourselves how a type can be encoded with a
representation, consider representing a list of |Int| with theese
types:
\begin{code}
data List = Cons Int List | Nil
\end{code}
This would be represented by the type:
\begin{code}
type Rep = (K Int otimes Id) oplus Unit
\end{code}

It is straightforward to see that the sum of constructors gets
translated to the |oplus| type. The |otimes| type is used to join the
arguments of the first constructor. One of the arguments is a
primitive |Int| represented with |K Int| and the second arguments is a
recursive ocurrence of the list, represented by |Id|. Finally, the
|Nil| constructor is represented by |Unit|.

To write generic functions in Regular, one must declare a type as an
instance of the Regular typeclass. The Regular typeclass is the following:
\begin{code}
class (Functor (PF a)) => Regular a where
  type PF a :: * -> *
  from :: a -> PF a a
  to :: PF a a -> a
\end{code}

The constituients of the class are a type called |PF| which simply is
the representation using the types of Regular and two functions |to|
and |from| that convert values to representations and representations
to values. For the case of the |List| provided above, an instance
could be the following:
\begin{code}
instance Regular List where
  type PF List = (K Int otimes Id) oplus Unit
  
  from (Cons i l) = Inl (K i otimes Id l)
  from Nil = Inr Unit

  to (Inl (K i otimes Id l)) = Cons i l
  to (Inr Unit) = Nil

\end{code}

This instance declaration is very unremarkable. In general, providing
an instance of Regular for a particular type is a mechanical process
and Template Haskell~\cite{TemplateHaskell} is used to automatically
derive them.

Generic functions can now be expressed in terms of values of
representation types instead of using values of the type itself. A
generic function is expressed as a typeclass and is implemented by
creating instances of type representations for that typeclass. To
illustrate this approach, the generic increment function will be
defined. This function increases by one the value of every integer
that occurs in a type. This is expressed by the following class:
\begin{code}
class GInc r where
  gInc :: r -> r
\end{code}
and is implemented as follows:
\begin{code}
instance GInc (K Int) where
  gInc (K i) = K (i + 1)

instance GInc Unit where
  gInc Unit = Unit

instance GInc Id where
  gInc (Id r) = Id $ from $ gInc $ to r

instance (GInc f, GInc g) => GInc (f oplus g) where
  gInc (Inl f) = Inl $ gInc f
  gInc (Inr g) = Inr $ gInc g

instance (GInc f, GInc g) => GInc (f otimes g) where
  gInc (f otimes g) = gInc f otimes (gInc g)

instance GInc (K a) where
  gInc x = x
\end{code}
This definition requires the Overlapping Instances extension (among
others) since there is no way to provide a specific case for |Int| and
a case for everything but |Int|. It can be observed that the |GInc|
function works for any representation given in terms of Regular's
types. To finalize the definition, a wrapper must be written:
\begin{code}
inc = from circ gInc circ to
\end{code}
This wrapper simply converts the value into the representation and
then converts the result back to a value.

\section{The F\# language}

The F\#~\cite{export:192596} programming language is a functional
language of the ML family. It started off as a .Net implementation of
OCaml but it has adopted and ignored many features in order to
inter-operate nicely with the .Net platform and its languages. One
notable feature of the language is that it obtains its type system
from the .Net platform (in other words there is no type
erasure). However, the language has constructs that allow type
inference, similarly as it happens with the Hindley-Miller system.

\subsection{Types and Type System}
The types in the F\# language can be divided into two categories. The
purely functional structures and the Object Oriented/Imperative
structures. The language is completely object oriented in the sense
that every value is an object. In some cases, the compiler will
optimize values by un-boxing primitive types (like integers) but this
happens transparently depending on how a value is used.

{\bf Functional types: }The functional structures are Algebraic Data Types and Records. Both
of theese structures are immutable and do not allow
inheritance/sub-type relations (they are sealed in .Net slang). ADTs
in F\# are very similar to those of a traditional functional
language. Type constructors are defined by cases along with the
arguments the constructor requires to build the type. Records are
defined by enlisting the fields of the record along with the type of
each field. Records can then be constructed by providing the arguments
of each of the Record's field as a name argument.


\part{Research Topic}
\section{Description of the Problem}
\label{sec:prob}
Even though datatype generic programming has existed for almost 20
years, little effort has been done to use it in languages other than
Haskell. The method is still quite unknown and if more languages could
adopt it, it could eventually become a tool to prevent boilerplate
code and unecessary refactoring within large software
systems. However, it is not trivial to translate the Haskell approach
to other languages, especially languages like F\# which lack
kind-polymorphism.

\subsection{Why should F\# adopt Datatype Generic Programming}
Programmers of the F\# language also face the problem of having to
define a function multiple times for every ADT. Apart from parametric
polymorphism and ad-hoc polymorphism, the language dosen't have a good
method to define generic functions.

When polymorphism isn't enough, the programmers rely on reflection to
define functions generically. There are several reasons why this
approach is inconvenient: 
\begin{itemize}
\item Reflection is quite involved to use. The programmer must learn a
  lot on how .Net internally handles types and values.
\item The F\# language offers no syntactic facilites to call functions
  via reflection. This means that a function call can ammount to
  several lines of code. 
\item Reflection relies on dyamic typeing which can lead to runtime
  errors. 
\item Different implementations (eg. .Net and Mono) handle reflection
  differently so code might not work in every platform.
\end{itemize}

It is generally easier and less time consuming implementing a function
tens of times before recurring to reflection. The average programmer
will hardly find it convenient to use reflection, cluttering the
codebase with boilerplate code in the long run. Reflection also lacks
the mathematical elegance of inductively defined functions which,
combined to the disadvantages above, easily leads to code that is hard
to mantain.

Taking as inspiration the existing knowlege about datatype generic
programming, it might be possible to construct a library that allows
the definition of generic functions with out requiring the programmer
to use reflection. Even if this library is implemented using
reflection, the programmer would enjoy several advantages using it:
\begin{itemize}
\item The definition of generic functions will not require reflection
\item The code that uses reflection can be small and easier to mantain
\item The library can perform optimizations which would have to be
  done manually when using reflection
\item Defining and calling generic functions has little overhead for
  the programmer since it will be done elegantly, inductively and
  without the syntactic clutter of code that uses reflection
\end{itemize}

The existing methods for datatype generic programming cannot be
directly implemented in F\# since the language lacks features that are
heavily used by said methods. The remainder of the section outlines
what are those features and their role in datatype generic
programming.

\subsection{Kind-Polymorphism and Datatype Generic Programming}

Kind-polymorphism is an \emph{essential} component for datatype
generic programmer. Recall that the idea is to abstract over type
constructors and define functions using such abstraction. Since type
constructors usually take other type arguments one must necesarily
abstract over types of higher kind. In other words, |C a| where |C| is
a type variable that abstracts over type constructors is of kind |(*
-> *)|.

\subsection{Dependent types and Generic Programming}
Dependent typeing is a language feature that allows a language to
determine the type to which a type variable gets instantiated based on
the types other type variables were instantiated. In Regular, this
is an essential feature to provide type safety. Recall the Regular class:
\begin{code}
class (Functor (PF a)) => Regular a where
  type PF a :: * -> *
  from :: a -> PF a a
  to :: PF a a -> a
\end{code}
Notice that |PF| is a function over types defined by cases every time
an instance of the Regular class is declared. The compiler only needs
to know what the variable |a| is and then it replaces |PF a a| with
the type representation of |a| which is provided as part of the
definition.

Thanks to this feature, the compiler can ensure that only well formed
representations will be produced or consumed by the |to| and |from|
functions.

The F\# language lacks a similar method for type level
programming. The closest feature of the language is type-providers but
due to several restrictions (outlined in section \ref{sec:tp-res}),
they can't be used to immitate this feature.

\subsection{Typeclasses and Generic Programming}
Typeclasses are another Haskell specific feature essential for generic
programming. They are the mechanism used in Haskell for function
overloading. The special feature about typeclasses is the way they
select function overloads. Consider the following portions of the
|GInc| function:
\begin{code}
instance GInc (K Int) where
  gInc (K i) = K (i + 1)

instance GInc Unit where
  gInc Unit = Unit

instance (GInc f, GInc g) => GInc (f oplus g) where
  gInc (Inl f) = Inl $ gInc f
  gInc (Inr g) = Inr $ gInc g
\end{code}
Consider what happens when |gInc| is invoked with a value of type |f
oplus g|. The function invokation makes a recursive call to an
overload of |gInc| -- but which? It is not possible to determine the
precise overload until all type variables get instantiated. For
instance, |gInc| can be called with a value of type |K Int oplus Unit|
as well as a value of type |Unit oplus Unit| or even |GInc a => a
oplus K Int|. Each of theese scenarios leads to different selections
of the |gInc| overload. Haskell addresses the problem by performing
type level computations when type variables get instantiated to select
the correct overload.

F\# does not have the ability to delay the selection of an overload
until a type variable gets instantiated. The closest approach is
method overriding but that can't be used since all the generic
methods would then have to be defined with the definition of the
representation types.

\section{Objectives}
To explore the feasability of implementing a datatype generic
programming in F\#, the following objectives are outlined:

{\bf General Objectives}
\begin{itemize}
\item Implementing a library for datatype generic programming using Regular as a basis
\item Compare the library to existing Haskell libraries
\item Evaluate the library
\end{itemize}

{\bf Specific Objectives}
\begin{itemize}
\item Define the types that will be used to define representations
\item Create a mechanism to automatically derive representations
\item Implement a mechanism to select method overloads using reflection
\item Outline the shortcommings resulting from the lack of kind polymorphism
\item Outline the shortcommings resulting from the lack of dependent types
\item Compare the library to Regular
\item Evaluate the library according to ``Comparing Libraries for Generic Programming in Haskell''~\cite{CompGen}
\end{itemize}

\part{Strategy to Solve the Problem}

\section{Representations in F\#}

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
\caption{Definition in F\# of all the types used to build type representations.}
\label{fig:rep-def}
\end{figure*}

The core of datatype generic programming libraries is the
representation type. As mentioned before, this library borrows its
approach from Regular but has to be modified to cope with the
limitations described in section \ref{sec:prob}.

All representations inherit from the class |Meta|. On a type level,
the role of this class is to impose type constraints on type
variables. Theese constraints are an alternative to the typeclass
constraints used in Regular. For example, consider the following
instance of the |GInc| defined above:

\begin{code}
instance (GInc f, GInc g) => 
  GInc (f :*: g) where
    gInc f (x :*: y) = ...
\end{code}

Rather than abstracting over higher-kinded type arguments, this
library abstracts over first-order type variables of kind |*| and
requires that they themselves are subtypes of the |Meta| class.

The concrete subtypes of |Meta| will be presented in the remainder of
the section. Theese sub-types are analogous to the representation
types already presented for Regular. All the subclasses of the |Meta|
class are parametrized by at least one (phantom) type argument, |`ty|.
This argument will be instantiated to the type that a value of type
|Meta| is used to represent.

The first subclass of |Meta| is |Sum|, that represents the sum of type
constructors, analogous to |oplus| in Regular. Besides |`ty|, it takes
two additional type arguments: |`a| and |`b|. It stores a single
element of type |Choice<<`a,`b>>| which contains two type
constructors: |Choice1Of2| and |Choice2Of2| which are used instead of
|Inl| and |Inr|.

The second subclass of |Meta| is |Prod|, corresponding to the product
of two types, analogous to |otimes| in Regular. Besides the |`ty|
argument, the |Prod| type accepts two additional type arguments:
|vara| and |varb| corresponding to the types of the two values of the
product. It contains the properties |E1| and |E2| to access each of
the elements of the product.

The third subclass of |Meta| is |K|, used to represent types that are
not defined as ADTs, analogous to |K| in Regular. In addition to |`ty|
it contains an extra argument |`a| which is the type of the value it
contains. The variable |`a| has no type constraints since F\# cannot
statically constrain a type to not be an ADT. The value contained in
|K| can be accessed by the property |Elem|.

The fourth subclass of |Meta| is |U|, used to represent empty type
constructors, analogous to |U| in Regular. It takes no additional type
arguments.

The fifth subclass of |Meta| is |Id|, used to represent recursion
within a type, analogous to |Id| in Regular. This type only contains a
single value of type |`ty| which is the recursively occurring value.

The definitions of these types are given in Figure~\ref{fig:rep-def}.
This definitions are not complete since the actual implementation
contains extra code used for reflection which is not relevant when
discussing the universe of types that the library can handle.

The List type defined above for Regular can also be defined in F\#
along with its representation:
\begin{code}
type List = Cons of int*Elems
            | Nil 
\end{code}
\todo{Finish this once the final impl is ready}
\begin{code}
type ListRep = 
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
\end{code}

\section{Defining generic functions as classes}

The purpose of type representations is to provide an interface that
the programmer can use to define generic functions. Once a function is
defined on all the subtypes of the |Meta| class, it can be executed on
any value whose type may be modeled using the |Meta| class.

Similar to Regular, generic functions will be defined by cases for
each of the types that define representations. Since F\# dosen't have
typeclasses, each case will be defined by overriding methods of the
abstract class called |FoldMeta|. The |FoldMeta| class is defined as
follows:
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

The |FoldMeta| type is parametrized by the following type argumetns:
\begin{itemize}
\item |`t| which is the type being represented by the type representation
\item |`in| which is the input type of the generic function
\item |`out| which is the output type of the generic function
\end{itemize}

In addition to those arguments, the |Sum|, |Prod|, |K| and |U|
variants of the method also include the type parameter |`ty|. Recall
that all type representatios take as first type parameter the type
being represented. In the case of 'nested types' or types that contain
within them other types, the parameter will vary in different sections
of the representation. Therefore, it is necessary to quantify over all
types, not only |`t|. Regular does not do this but it is necessary to
define certain generic functions which will be covered later. The |K|
override also contains the type parameter |`a| which denotes the
primitive type contained by |K|.

This class can only handle generic functions that take a single
argument. However, F\# allows types to have the same name as long as
they differ in the number of type parameters. This makes it possible
to define variants of |FoldMeta| that take more arguments.

To illustrate how the library works. The generic function |GMap| will
be used as an example. This function takes as an argument another
function and applies the function on every occurence of the type of
the function. The heading of the function is the following:

\begin{code}
type GMap<<`t,`x>>(f : `x -> `x) = 
  class 
  inherit FoldMeta<<
    `t,
    Meta>>()
  end
\end{code}

This function uses the variant of |FoldMeta| that accepts no input
arguments since the functional argument is moved to the
constructor. In cases where the argument does not change during the
recursive calls, it is easier to make the argument a class argument.
To perform the mapping, the function produces a new representation
with updated values; hence the |`out| parameter is instantiated to
|Meta|.

The first method that needs to be overriden is the |Sum| case: 
\begin{code}
override self.FoldMeta<<`ty>>
  (v : Sum<<`ty,Meta,Meta>>) =
    match v.Elem with
    | Choice1Of2 m -> 
      Sum<<`ty,Meta,Meta>>(
      self.FoldMeta(m) |> Choice1Of2)
    | Choice2Of2 m -> 
      Sum<<`ty,Meta,Meta>>(
      self.FoldMeta(m) |> Choice2Of2)
    :> Meta
\end{code}
The |Sum| constructor encodes the type constructor that was used to
create the value that was provided. The choice is encoded as nestings
of the |Choice| type and the nesting is defined by using the
|Choice1Of2| and |Choice2Of2| constructors. This override will
recursively apply the |FoldMeta| function to both cases and pack the
result back into a value with the same number of |Choice|
nestings. The result must be casted to |Meta| in order to agree with
the type of the method.

Next, the |Prod| case must be overriden:
The next definition handles products:
\begin{code}
override x.FoldMeta<<`ty>>
  (v : Prod<<`ty,Meta,Meta>>) =
    Prod<<Meta,Meta>>(
      x.FoldMeta(v.E1),
      x.FoldMeta(v.E2)
    :> Meta
\end{code}
The |Prod| type contains two properties, |E1| and |E2|, which
correspond to the two representations from which a product is
built. Again, the function only needs to be applied recursively to the
inner representations of the product and then packed back.

To handle the |K| constructor, two methods are needed:
\begin{code}
member x.FoldMeta<<`ty>>(
  v : K<<`ty,`x>>) = 
  K(f v.Elem) :> Meta

override x.FoldMeta<<`ty,`a>>(k : K<<`ty,`a>>) = k :> Meta
override x.FoldMeta<<`ty>>(u : U<<`ty>>) = u :> Meta
\end{code}

The first case handles the occurences of primitive values that have
the same type as the input type of the argument function. It simply
applies the function to the value and packs the result with the same
constructor. The second case handles all other values. Since nothing
can be done with them, they are returned as they are. Below is the
definition for the |U| type which dosen't do anything special either.

Next, the |Id| case must be overriden:
\begin{code}
override x.FoldMeta
  (v : Id<<`t>>) =
    let g = Generic<<`t>>()
    Id<<`t>>(x.FoldMeta(
      g.To c.Elem) |> g.From)
    :> Meta
\end{code}
Since this library works with shallow representations, recursive
values are not immediately converted to their representation. Since
generic functions only work with representations, the value must first
be converted to its representation, then |FoldMeta| can be recursively
applied to the representation and finally the resulting representation
is converted back to a value and packed inside the |Id| constructor.

Although the definition for |GMap| is complete, it is still
incorrect. As it stands, it only allows primitive values to be
mapped. Values that are expressible as a representation (ADTs) will
not get mapped, just ignored. The reason is that such values get
translated into their corresponding representation when the generic
funciton gets applied. Here is were the first parameter of
representation types becomes important. Three additional overloads are
provided to map ADTs:

\begin{code}
let mapper (f : `x->`x) (v : Meta) =
  let g = Generic<<`x>>()
  v |> g.From |> f |> g.To

member x.FoldMeta(
  u : U<<`x>>,f : `x->`x) = mapper f u
member x.FoldMeta(
  p : Prod<<`x,Meta,Meta>>,f : `x->`x) = mapper f p
member x.FoldMeta(
  s : Sum<<`x,Meta,Meta>>,f : `x->`x) = mapper f s
\end{code}
Theese overloads match the type parameter of the representation type
with the type of the first argument of the input function. When the
match is positive, the function proceeds by calling the |mapper|
helper function which converts the representation into a value,
applies the function and converts the result back into a
representation. Theese overloads no longer have the universally
quantified |`ty| parameter since they work specifically for the type
|`x| which gets instantiated at a class level rather than being
instantiated when the method is invoked.

The definition is now correct and complete. If implemented with the
library, it will generically map algerbaic data types. The following
sections explain how the library correctly selects the methdos that
are invoked in each case. Note that all recursive calls of the
|FoldMeta| method invoke the overload with signature |FoldMeta : Meta
-> `out| for which no implementation was given. The implementation of
the method is derived automatically using reflection and will be
explained in section \todo{reference section}.

\section{Overload selection}

The |GMap| function defined above has overlapping overloads -- cases
where several methods can be invoked for a particular value. This is a
problem that many datatype generic libraries have. In the case of
Haskell base libraries, the problem is generally solved by enabling
the overlapping instances language extension.

In the case of F\#, the problem must be approached differently. For
starters, all overload selections must be statically resolved before
at compile time (as mentioned in section \ref{xx} \todo{add ref to
  overload selection}). This, in principle, makes a feature such as
overlapping instances usleless in F\#. However, this also restricts
the library from allowing functions like |GMap| to be defined, which
demand that a similar feature exists. To resolve the problem, a
customized dispatch mechanism is implemented using reflection. This
mechanism inspects at runtime, the types of the arguments provided to
the |FoldMeta| method and selects the correct overload based on rules:

\begin{tabular}{cccc}
\multirow{15}{*}{|self.FoldMeta(m : Meta)|} & \multirow{15}{*}{$=\left\{\begin{array}{c} \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \end{array}\right.$} & \multirow{2}{*}{|self.FoldMeta(m)|} & |exists self.FoldMeta : tau->tau1| \\
& & & $\wedge$ |m : tau| \\
& & & \\
& & \multirow{4}{*}{|self.FoldMeta<<tau_a>>(m.Cast())|} & |self.FoldMeta<<`ty>> : tau'->tau1| \\
& & & $\wedge$ |m : tau<<tau_ty,tau_m1,tau_m2>>| \\
& & & $\wedge$ |tau_m1 :> Meta| $\wedge$ |tau_m2 :> Meta| \\
& & & $\wedge$ |[tau_ty/`ty]tau' = tau<<tau_a,Meta,Meta>>| \\
& & & \\
& & \multirow{3}{*}{|self.FoldMeta<<tau_a>>(m)|} & |exists self.FoldMeta<<`a>> : tau'->tau1| \\
& & & $\wedge$ |m : tau<<tau_ty,tau_a>>|\\
& & & $\wedge$ |[tau_a/`a]tau' = tau<<tau_ty,tau_a>>|\\
& & & \\
& & \multirow{3}{*}{|self.FoldMeta<<tau_ty,tau_a>>(m)|} & |self.FoldMeta<<`ty,`a>> : tau'->tau1| \\
& & & $\wedge$ |m : tau<<tau_ty,tau_a>>|\\
& & & $\wedge$ |[tau_ty/`t][tau_a/`a]tau' = tau<<tau_ty,tau_a>>|\\
& & & \\
%% & & | = o.Sum(x : Sum<<tau,Meta,Meta>>,v1 : tau1,...,vn : taun)| \\
%% & & |self.Sum(x : Meta,v1 : tau1,...,vn : taun)| \\
%% & & | = o.Sum<<tau>>(x : Sum<<tau,Meta,Meta>>,v_1 : tau1,...,v_n : taun)|
\end{tabular}
where
\begin{itemize}
\item |tau1 :> tau2| indicates that |tau1| is a sub-type of |tau2|
\item |[tau1/tau2]tau| indicates replacing |tau2| with |tau1| in |tau|
\end{itemize}

This selection mechanism is very simple and it replaces the type level
computations carried out by the Haskell compiler in order to select
the right overloads. The process happens in stages. First the method
|FoldMeta : Meta->`out| is invoked with an argument of type
|Meta|. Recall that |Meta| is an abstract class so all values of type
|Meta| also have some other type |tau :> Meta|. To select the
overload, first one checks if there is a method |FoldMeta : tau ->
`out|, if such method exists, invoke the method with the supplied
arguments. If the previous check fails, type variables are
instantiated in order to invoke a suitable generic method. This
happens by cases:
\begin{itemize}
\item When |m : U<<tau_ty>>|, methods of type |FoldMeta : forall tau
  . U<<tau>> -> `out| are considered and |tau| is instantiated to |tau_ty|
\item When |m : K<<tau_ty,tau_a>>|, methods of type |FoldMeta : forall
  tau1,tau2 . K<<tau1,tau2>> -> `out| are considered. |tau1| is
  instantiated to |tau_ty| and |tau2| is instantiated to |tau_a|.
\item When |m : Sum<<tau_ty,tau_a,tau_b>> -> `out| or |m :
  Prod<<tau_ty,tau_a,tau_b>> -> `out|, methods of type |m : forall tau
  . Sum<<tau,Meta,Meta>> -> `out| or |m : forall tau
  . Prod<<tau,Meta,Meta>> -> `out| are considered. |tau| is
  instantiated to |tau_ty|. The inner types |tau_a| and |tau_b| are
  casted to |Meta| in order to make the method call compatible. 
\end{itemize}

When many methods with compatible signature exist. Priority is first
given to the colosest match and then the position in the class
hierarchy of the type that declared the selected method. Although this
mechanism is immitating the overlapping instances mechanism of the
Haskell compiler, it gives the user a finer control on which method is
selected. In fact, this makes it trivial to extend or customize
generic functions. For example, to define a function |GMapShallow|
which does the same as |GMap| but does not traverse structures that
occurr recursively one can simply extend from |GMap| and override the
|Id| case:
\begin{code}
type GMapShallow<<`t,`x>>(f : `x -> `x) = 
  class 
    inherit GMap<<`t,`x>>(f)

    override self.FoldMeta(v : Id<<`t>>) = v

  end

\end{code}

Here both functions can exist in the same namespace and context. In
fact, a function could invoke both of them as if they were any two
generic functions.


\end{document}

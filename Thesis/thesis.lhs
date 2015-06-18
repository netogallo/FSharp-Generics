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


\subsection{Generic Programming with Regular}

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

\end{document}

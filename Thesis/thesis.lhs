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

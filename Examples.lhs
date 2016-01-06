
\begin{code}
data E a
  = E1 a
  | E2
  | E3 a a

typeDeltas 'forward 'backward [
  [t|forall a. E a|] :->:
    ([r|E1, E2, E3 E3', s/^E/T/i|] >>= f)
    [d|data E' a = E3' E' T | E4 E |]
]
\end{code}

You can do this for multiple types simutaniously as follows

\begin{code}
data T a = T1 (E a) | T2

data E a
  = E1 a
  | E2
  | E3 a a

typeDeltas 'forward 'backward [
  [t|forall a. E a|] :->:
    ([r|E1, E2, E3 E3', s/^E/T/i|] >>= f)
    [d|data E' a = E3' E' T | E4 E |],
  [t|forall a. T a|] :->:
    ([r|E2|] >>= f)
    [d|data T' a = |]
]
\end{code}

\begin{code}
typeDeltas 'forward 'backward [
  [t|forall a. E a|] :->:
    [r|E1, s/^E/T/i|]
    [d|data E' a = E3'|],
  [t|Set E|] :~>: [t|Set E'|] [|setTransform|],
  [t|Map E E|] :~>: [t|Map E' E|] [|mapTransform1|],
  [t|Map E E|] :~>: [t|Map E' E'|] [|mapTransform2|]
]
\end{code}


\subsection{Omitting functions}

We can use variations of the \code{:->:} operator so
that either or both of the manually-written user function
and the returned generated function can be omitted.

\begin{code}
data T a = T (E a)

data E a
  = E1 T
  | E2
  | E3 a a

typeDeltas 'forward 'backward [
  [t|forall a. E a|] :->:
    ([r|E1, E2, E3 E3', s/^E/T/i|] >>= f)
    [d|data E' a = E3' E' T | E4 E |],
  [t|forall a. T a|] :-:
    f
    [d|data T' a = |]
]
\end{code}

In this example, \code{forward} has the following type.

\begin{spec}
forward :: (E a -> E' a) -> (E a -> E' a)
\end{spec}

If we had used \code{:->:} instead of its varient,
\code{forward} would have had the following type.

\begin{spec}
forward :: (E a -> E' a) -> (T a -> T' a) -> (E a -> E' a, T a -> T' a)
\end{spec}

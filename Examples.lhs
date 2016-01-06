
\begin{code}
data E a
  = E1 a
  | E2
  | E3 a a

delta 'forward 'backward [
  [t|forall a. E a|] :->:
    ([r|E1, E2, E3 E3', s/^E/T/i|] >>= f)
    [d|data E' a = E3' E' T | E4 E |]
]
\end{code}

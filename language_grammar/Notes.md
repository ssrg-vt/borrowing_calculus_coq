# Information related to effects:

- Langauge has a strict semantics where arguments are evaluated before calling a function (unlike as Haskell's  lazy evaluation). 
- Side effects can occur only during the function application.
  ``` (t1, t2, ..., tn) -> e t```
  A function with arguments of type t1, ..., tn produces an effect e and return value type as t.
- Functions need to be fully applied and are not curried. This makes it immediately apparent where side-effects can occur. f x y = (f(x))(y)


## Effects of our interest:
- Basic effects:
    - Div : Divergence/ Non-termination 
    - Exn : Exception
- Koka uses termination analysis based on inductive types to assign ```div``` effect to recursive functions that cannot terminate. 
    - Each recursive call decreases the size of the inductive data type. 

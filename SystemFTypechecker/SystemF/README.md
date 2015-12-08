# Typechecking for System F

Given some context and raw annotated term the program computes term's type in the specified context or says that the term cannot be typed in the context. Note that no α-conversion is performed so the term λx:Nat.x cannot be typed in the context G={x:Nat} because a correct context cannot contain repeated bindings with the same names. But λy:Nat.y can be typed in G.

`SystemF` module contains type inference implementation with the main function called `infer`.

`Tests` module contains tests and utils to construct context from the list of bindings and run typechecking. To run tests, first load the module in emacs by typing `C-c C-l`. Then use `C-c C-n nameOfTheTest RET` to make emacs show the value of the nameOfTheTest binding (which is a test result).

To write your own tests you need the following unicode symbols:

* ▴ is \\tb3 (dot in lambdas)
* ⇒ is \\=> (arrow in  function types)
* ∷ is \\:: (list's cons constructor)
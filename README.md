A study of <ins>**ba**</ins>lanced <ins>**bi**</ins>nary <ins>**sea**</ins>rch <ins>**t**</ins>rees, using OCaml's GADTs to encode their invariants and drive the implementation.

Since the typechecker ensures that trees are always balanced, this leads to straightforward code for `add` and `remove` as there's no need to "repair" broken trees (which is a really hard process to check for correctness).  Furthermore, we get a lot of assistance from the OCaml typechecker while we write the code -- both to guarantee that we produce valid trees, but also to identify which code doesn't need to be written!

It's pretty crazy how much of a killer feature GADTs are, when they enable such complex code to be written without a textbook or even unit tests. In case you want to replicate this experiment, here's the general strategy:

1. Encode the datastructure invariants in a GADT. For example, red-black trees require that:
   - Leaves have `zero` height and are painted `black`
   - Red nodes have two `black` children of the same `height`
   - Black nodes have two children of the same `height` but of any `_` color
   - Only black nodes are counted when measuring the `height` of the binary tree
   
   This neatly translates into the following GADT:
   
   ```ocaml
   type ('height, 'color) tree =
     | Leaf : (zero, black) tree
     | Red : ('height, black) tree * elt * ('height, black) tree -> ('height, red) tree
     | Black : ('height, _) tree * elt * ('height, _) tree -> ('height succ, black) tree
   ```
   
   From then on, the OCaml typechecker will ensure that you can never produce or manipulate an invalid red-black tree!
   
   On a side note, red-black trees are infamous for their complexity -- you'll have an easier time if you start with 2-3 trees to familiarize yourself with the technique.

2. To write the `add` insertion function on this tree, you'll first need to figure out its type:

   ```ocaml
   val add : elt -> ('height, 'color) tree -> (???, 'color) tree
   ```
   
   The `???` height in the return type is an issue: it would be really convenient if you could return a tree of the same height and color as the input, however it should be clear that a tree of fixed height can only contain a bounded number of elements. At some point, you will need to increase the height of the tree by one to accommodate more values. With this in mind, you can introduce another GADT to type the return value of the `add` function:
   
   ```ocaml
   type 'height add_result =
     | Ok       : ('height,      _) tree -> 'height add_result  (* Ok, same height! *)
     | Overflow : ('height succ, _) tree -> 'height add_result  (* Not enough room, must increase the height! *)
   
   val add : elt -> ('height, 'color) tree -> 'height add_result
   ```
   
   You can now start implementing the `add` function, with assistance from the typechecker and exhaustivity checker to identify all the cases that you need to cover. Note that the `add` function is a bit verbose since you need to do a binary search in the tree, but at first you can keep things manageable by only implementing *"insert at left-most position in the tree"* as if the element was smaller than anything else, since the other case is symmetric.
   
   After some busy work, you'll discover that you need to pattern match deeper and deeper to handle all the cases... and that this process keeps on producing more unhandled cases, without a clear end to the madness in sight. It's now time to step back and take a look at your uses of the `Overflow` constructor: you should be able to see that you only ever produce values with shape `Overflow (Black (Red (_, _, _), _, Black _))` and `Overflow (Black (Black _, _, Red (_, _, _)))`.
   
   Hence you can restrict the type of the `Overflow` constructor to cover only those two patterns:
   
   ```ocaml
   type 'height add_result =
     | Ok       : ('height, _) tree -> 'height add_result
     | Overflow : ('height, black) tree     (* Inlined the three black children a,c,e of *)
                * elt                       (*    Black (Red (a, b, c), d, Black _ as e) *)
                * ('height, black) tree     (* ~= Black (Black _ as a, b, Red (c, d, e)) *)
                * elt
                * ('height, black) tree
               -> 'height add_result
   ```
   
   And suddenly, the typechecker will make a bunch of problematic cases obsolete! (and even encourage you to delete working dead code!) The remaining unhandled cases can also be discarded by observing that `Overflow` values are only produced when inserting into a `Red` node: By restricting its use to this color only, the exhaustivity checker will kindly detect more dead cases and allow you to complete the implementation.
   
   ```ocaml
   type ('height, 'color) add_result =
     | Ok       : ('height, _) tree -> ('height, _) add_result (* Always allowed *)
     | Overflow : ('height, black) tree
                * elt
                * ('height, black) tree
                * elt
                * ('height, black) tree
               -> ('height, red) add_result (* Only allowed when inserting in a Red node *)
   
   val add : elt -> ('height, 'color) tree -> ('height, 'color) add_result
   ```

   Since it's more fun to discover these GADT restrictions in your own code, this isn't quite the final type -- just a hint towards the solution! But you can always check out the example implementation if you get stuck. Note that red-black trees introduce some extra complexity with their color parameter, a difficulty that doesn't exist with other BSTs.

   When reading code which uses GADTs, one might believe that the code was automatically derived from a pristine GADT written beforehand. In practice it's really hard to define the perfect GADT from scratch, but it can be naturally evolved from a dialogue with the typechecker: when encountering a case that's hard to implement, you can refine the GADT definition to get rid of it! This in turn will require you to fix some other parts of your code, but you'll eventually converge on both the perfect GADT for your problem and the code that uses it.
   
3. The `remove` operation follows the same strategy. This time there's no risk of overflowing the tree height, but you may have to reduce its height by one:
   
   ```ocaml
   type 'height remove_result =
     | Uk        : ('height, _) tree -> 'height      remove_result (* Ok, same height! *)
     | Underflow : ('height, _) tree -> 'height succ remove_result (* Too much space available, must shrink! *)
   
   val remove : elt -> ('height, 'color) tree -> 'height remove_result
   ```
   
   While this function requires a lot more code, there's a bit less ingenuity required on the GADT side. Are you disappointed you didn't get to read the missing Okasaki's tutorial on how to remove an element from a red-black tree? But now you don't need it!


*This repo is released in the public domain (or equivalent), in case you need a self-contained BST implementation to build upon :)*

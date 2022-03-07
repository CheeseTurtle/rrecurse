# Overview

`rrecurse` ("rainbow recurse") is an SWI-Prolog module(-in-progress) that provides a couple of easy-to-use "rainbow recurse call" meta-predicates, `rrcall/1` and `rrcall/2`. These provide developers with a simple yet robust way to add trace output to any recursive predicate. They can be used to call any goal that contains a recursive predicate. It works very similar to `call(...)` with the key difference being that the optional second argument is not appended to the goal arguments, but rather allows the user to specify the "head template" that should be matched as the recursive predicate to rainbow-ify. These predicates have the potential to be useful in many situations involving recursion in SWIPL code.

## Features and Screenshots

* Shows the progressive unification of terms at every level of recursion, color-coded and with clear indentation. Note epecially that for maximum clarity and insight, the head and tail are kept separate in the lines showing the values of the predicate arguments when leaving each level, and then shown combined when reporting that the predicate was successfully called from the previous level. That is, within each predicate, *the definition of that predicate's arguments as per the head of the clause being visited* is reflected in how its trace line is printed, whereas the lines showing the predicate call and the resulting bindings, as seen by the calling context, print the arguments *as seen from the calling context* (with no regard to the clause heads).

  ```prolog
  mytest([], []) :-
    !.
  mytest([H|T], [H|R]) :-
    mytest(T, R).`
  ```
  ![image](https://user-images.githubusercontent.com/4154751/156992183-9adc5ef8-8e21-40b0-8379-680eb560925a.png)

* Works with any[^1] predicate written in SWI-Prolog, includig built-ins! (Foreign predicates not supported.) Using this module is both simple and convenient.
  ![image](https://user-images.githubusercontent.com/4154751/156995634-23deac98-7251-4672-a3b2-116ddff589b5.png)
  ![image](https://user-images.githubusercontent.com/4154751/157102354-6bd2d908-621e-4166-9d3f-00ec5144fe35.png)



[^1]:
    Well, it hopefully will in the future. There are currently still some issues with certain predicates that the dependencies `rrecurse` (and/or the dependencies' dependencies) use, such as `lists:append/3`. Fortunately, for most of these predicates it is not difficult at all to simply copy to a new file the source code for the predicate you'd like to rainbowify, rename the predicate, and then simply rainbowify the newly-named predicate.

## FAQs

1. **Who should use this module?** 

   As it is not yet perfectly functional, I disrecommend using it unless you are either knowledgeable to understand how it works (or, rather, why it doesn't, lol), or are okay with sometimes inexplicable behavior.

3. **Is this module complete?** 

    Sadly, no. There are a couple of oddities that need to be smoothed out, mostly relating to the module's reliance on attributed variable hooks to trigger the "`after_enter`" `print_call/4` call.

6. **What problems might the user face due to its imperfect status?**

    When the rainbow-ified predicate is called in the goal from within another recursive predicate, the printing of certain subsets of recursion layers is in some cases "delayed". This is also more likely to occur when arguments are supplied to the recursive predicate that are nonvar and nonground --that is, they are bound to a term that contains (unbound) variables.
    
    ![image](https://user-images.githubusercontent.com/4154751/156991736-4b02c71c-cddd-4fe4-9b3a-1bbbb7b0596a.png)
    ![image](https://user-images.githubusercontent.com/4154751/157104421-6d914eda-f9e9-4c5d-b189-0bf70e05d0a1.png)
    
    Using `rrcall/1` or `rrcall/2` currently sometimes makes otherwise deterministic goals non-deterministic. There is likely no surefire way to avoid this unfortunate side-effect until I manage to eliminate the addition of superfluous choice-points.
      ![image](https://user-images.githubusercontent.com/4154751/157105824-45a89757-fdce-46e2-9742-8ae25697a6af.png)
    
8. **Will more features be added in the future?**
    
    Yes! I have a few ideas for additional customization capability, potentially by defining hooks. I'd also like to find a way to (optionally?) provide more visual feedback for the backtracking, most likely by making use of the `undo/1` built-in. But first, I really need to fix the issue I mentioned in the answer to Question 3.


# Invocation Syntax
* **`rrcall/1`:** `rrcall( Goal )`
* **`rrcall/2`:** `rrcall( Goal, Template )`

| Argument Name | Accepted Value Type | Description | Example(s) |
| :-----------: | :------------------ | :---------- | :--------- |
| `Goal`        | callable            | Any syntactically valid term you would pass to `call/1` | `pred(A1,A2)`, `(X>Y -> pred(A1,A2) ; pred(A3,A4))` |
| `Template`    | atom or compound    | Must match the head of the recursive predicate you'd like to rainbow-ify. See notes on template-matching behavior above. | `pred(A1,A2)`, `module:pred(A1,A2)`|
|               | predicate indicator | A predicate indicator describing a defined, visible, interpreted, and non-foreign predicate. The module may be omitted, in which case `rrecurse` will try to determine a module by matching the incomplete indicator with those of an eligible known predicate. In all cases, both name and arity must be specified. | `pred/2`, `module:pred/2` |


# Overview

`rrecurse` ("rainbow recurse") is an SWI-Prolog module(-in-progress) that provides a couple of easy-to-use "rainbow recurse call" meta-predicates, `rrcall/1` and `rrcall/2`. These provide developers with a simple yet robust way to add trace output to any recursive predicate. They can be used to call any goal that contains a recursive predicate. It works very similar to `call(...)` with the key difference being that the optional second argument is not appended to the goal arguments, but rather allows the user to specify the "head template" that should be matched as the recursive predicate to rainbow-ify. These predicates have the potential to be useful in many situations involving recursion in SWIPL code.


## FAQs

1. **Who should use this module?** 

   As it is not yet perfectly functional, I disrecommend using it unless you are either knowledgeable to understand how it works (or, rather, why it doesn't, lol), or are okay with sometimes inexplicable behavior.

3. **Is this module complete?** 

    Sadly, no. There are a couple of oddities that need to be smoothed out, mostly relating to the module's reliance on attributed variable hooks to trigger the "`after_enter`" `print_call/4` call.

6. **What problems might the user face due to its imperfect status?**

    The only real issue that I haven't managed to resolve yet is that sometimes the first-layer call prints "late". You can tell that it's late because of the indentation briefly jumping back several levels. It doesn't make the module completely useless but it's definiely not helpful.

8. **Will more features be added in the future?**
    
    Yes! I have tons of ideas for additional customization capability, potentially by defining hooks. I'd also like to find a way to (optionally?) provide more visual feedback for the backtracking, most likely by making use of the `undo/1` built-in. But first, I really need to fix the issue I mentioned in the answer to Question 3.
    

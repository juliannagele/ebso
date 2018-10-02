* Abstract enc_instruction over number of elements added and deleted on stack

* Refactor evmenc; split into modules

* For now we assume that the stack is empty at start. This won't work
  when we optimise snippets of a smart contract. However, for a given
  snippet, we can always compute how deep this snippet looks into the
  stack. We can then all-quantify over that many stack entries.

  Example: Assuming we look 3 deep into stack, e.g., with [ADD; ADD]

  forall x0 x1 x2 =
    stack(0)(0) = x0
    stack(0)(1) = x1
    stack(0)(2) = x2

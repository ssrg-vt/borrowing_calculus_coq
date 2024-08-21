# Substructural Type Systems:
- Substructural type system augment standard type abstraction mechanisms with the ability to control the number and order of uses of a data structure or operation. 
- It is particularly useful for constaining interfaces that provide access to system resources such as files, locks and memory as these resources undergo a series of changes of state throughout its lifetime. For example, a memory my be allocated or deallocated, files may be open or close etc. Substructural type systems provide sound static mechanism for keeping track of just these sorts of state changes and preventing operations on objects in an invalid state.

## Linear Type System:
- Linear type systems ensure that objects are used exactly once, so it is completely obvious that after the use of an object, it may be safely deallocated. 
- Invariants of the linear type system:
    - Linear variables are used exactly once along every control-flow path. 

      ```
         (f(x,y) = <free z, free y>) x x
      ```
      Function free uses its arguments and then deallocates it. Now, if we allow linear variable (say x) to appear twice, a programmer might write 
      ```free x, free x``` This case leads to the situation where the program ends up attempting to use and then free x after it has already been deallocated, causing the program to crash.
    - Unrestricted data structures may not contain linear data structures. 
      More generally, data structures with less restrictive type may not contain data structures with more restrictive type.

      ```
        let z = un <x,3>  in 
        split z as x1,_ in 
        split z as x2,_ in 
        <free x1, free x2>
      ``` 
      In the above example, the pair <x,3> has qualifier unrestricted and the variable x has qualifier linear. But we could see that we end up freeing the memory twice. 

Lab 3 Writeup: Andrew Gordon, Noah Dillon

For questions that require implementation of code, see Lab3.scala

1.a.  Test case that behaves differently under big step and small step:

The following javascripty example returns two different values under dynamic scoping, implemented by our Big Step interpreter, and static scoping, implemented by our Small Step Interpreter:

```javascript
const x = 7; function(x){return function(y){ return x + y }}(2)(40)
```

This returns 47 and 42.  47 is the result of dynamic scoping.  The const declaration extends its value to the next environment where it can be evaluated in function(x).  42 is the result of small step, where in the scope that calls the function we do not see the const declaration and instead substitute the value 2 for x.  

2.c.  Explain whether the evaluation order is deterministic as specified by the judgement for e -> e'

Yes, it is deterministic.  This is because the rules are clearly defined as to where certain values can be stepped upon.  For example, a given e might only be stepped upon when it is in the form where all other items in the judgement or values.  In other words, the judgements always create the same parse tree, and are therefore deterministic.

3.  Consider the small-step operational semantics for JavaScripty shown in figures 7,8 and 9.  What is the evaluation order for e1 + e2?  Explain.  How do we change the rules to obtain the opposite evaluation order?

In the judgements defined for this lab, e1 + e2 is left associative.  We can see this in our SearchBinary rules.  In the form (e1) bop (e2), we can see that e1 must be stepped upon until we yield a v1 before we can step upon e2.  This yields a left associative equation.  To switch this we would do the opposite and step upon e2 until we yield v2 before stepping upon e1.  Programatically, we can see this in our case Binary in which we have the rule:

```scala
if (isValue(e1)) Binary(bop, e1, step(e2)) else Binary(bop, step(e1), e2)
```

4. a.  Give an example the illustrates the usefulness of short-circuit evaluation.

A useful short-circuit would be one that avoids evaluating a lengthy right-hand side equation when we do not have to.  For example,
```javascript
0 && factorial(10)
```
would produce a lengthy factorial calculation if we do not short circuit, when we already know the equation will return false.

b.  Does e1 && e2 short circuit?  

Yes, it does.  In the evaluation forms of DoAndTrue/DoAndFalse, we see that in the case that e1 is a value and is true, we then evaluate e2.  However, in the case that v1 is false, we simply return v1 and do not evaluate e2.  This is a judgement rule for a short circuit.
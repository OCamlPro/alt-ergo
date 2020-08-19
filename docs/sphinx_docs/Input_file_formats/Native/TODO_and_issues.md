 
# TODO and issues

TODO
1. Triggers
    * Make work, test and explain interval triggers (`{ [...] }`)
    * Be more precise on their semantic (exactly when will a trigger be called)
2. Theories
    * Make work, test, and explain how to use theories
    * `case_split` keyword
    * Test and explain semantic triggers (`in` intervals, `|->`)
3. BNF for everything (syntactic definition of declarations+expressions, with few comments)
4. Floats
5. Misc
    * Details on implementation of basic types
    * More examples on non-linear arithmetic
    * Check if records can be created inline
    * Check exactly what `rewriting` does
    * Check that `cut/check` don't work

Issues/Notes
1. Bool/prop partially merged
    * Two keywords for basically the same semantic
    * Different syntax
    * Only predicates can be used in `rewriting`
2. (Float must be loaded as a preamble)
3. The online version of TAE is in an older version of AE
    * For example, bool/prop not merged
4. Triggers are accepted in goals without raising warning
5. Cut/check don't seem to be supported

# CSci 5161 Intro to Compiler: Tiger Compiler

## Homework 3: Parser
### Usage
```
CM.make "sources.cm";
Parse.parseandprint "_tig_source_file_" "_output_file_";

```

### Conflict
None

### Potential Problem
"Shift-Reduce Conflict" might cause ambiguous grammar. There would be more than one way to understand the same statement and the different understanding ways would probably result in different outputs though the original statement is identical. Thus, we should reduce the number of Shift-Reduce Conflict as much as possible.

### Issues Met and Ways to Resolve
1. `lvalue[exp] (ID[exp])` and `ID[exp] of ID` has the same prefix. In order to avoid the conflict, I discussed it with classmates and the TA, then conclude a high efficient way which is to let the lvalue to detect more things. This would help Yacc know whether there exists `OF` to let the statement become a `Array Creation` expression, or just a l-value statement. I used a recursive definition to create a temp list to store the following statement then used a recursive function to retrieve them back from the list.
2. We'd like to see a single `exp` as a single `exp` rather than a list with just one element while it appears between left parenthesis and right parenthesis. I used a if-statement to consider the length of the list. If the length is 1, my parser would return a single `exp` instead of a list with just one `(exp, pos)` element, which keeps the same rule with the output file in `correct_output` folder.
3. I added special precedences for negative integer, function declaration and type declaration (which represented in `NEG`, `FUNDEC` and `TYDEC` respectively). I gave negative integer the highest precedences since it's a self-operator, which should be calculated first. Then I gave the function declaration and type declaration the lowest precedence, which would avoid all other rules and take actions at last. These will make sure function and type declaration would always have the all reduced cases except themselves, this can help avoid shift-reduce conflict issues and also truly prevent the situation that the parser isn't actually sure what should be shifted.

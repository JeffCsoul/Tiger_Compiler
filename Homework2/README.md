# CSci 5161 Intro to Compiler: Tiger Compiler

## 1. Homework 2: Lexical Analysis
### Usage
```
CM.make "sources.cm";
Parse.parse "_tig_source_file_";

```
### Description
1. For all reserved words, operators, integers and variables name, I used the INITIAL state to start the Regex matching.
2. When the program met `/*` symbol, the Regex state would be changed into STRING state and try to match all valid characters (except invalid characters starting with `\` and newline symbol `\n`). I used a global ref variable to record all the characters matched before another `"` symbol and another global boolean ref variable to check whether this string recorded is valid.
3. For matching more efficiently, I added another two states called SLASH and SLASH_M. SLASH is used to match the first character following escape character `\`. When the first try for matching fail, the state would be changed into SLASH_M for potential multi-lines string matching. I used another global boolean ref variable called format_flag for checking whether the at least one required format character (space, `\f`, `\t`, `\n`) is existent.

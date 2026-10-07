# Parsing: lexer, layout, parser (adamas-parser).
#
# A literal brace is written in Fluent as {"{"} and {"}"}.

lex-unexpected-char = unknown character
lex-unterminated-comment = unterminated comment `{"{"}-`
lex-unterminated-string = unterminated string literal
lex-unknown-escape = unknown escape in a string
lex-tab-in-indentation = tab in indentation: indentation is significant, tab width is not

layout-shallow-block = a block body must be indented further than the enclosing block
layout-empty-block = no block body after the keyword
layout-left-of-file = token left of the first one in the file: the file block closes only at the end of the file
layout-block-in-brackets = block inside brackets: layout is off there (§10 question 55)
layout-unclosed-bracket = unclosed bracket
layout-unmatched-bracket = closing bracket without an opening one
layout-mismatched-bracket = bracket closed by the wrong kind of bracket

token-ident = identifier
token-operator = operator
token-nat = natural literal
token-float = floating-point literal
token-str = string literal
token-open = start of block
token-sep = block boundary
token-close = end of block
token-eof = end of file

expected-declaration = a declaration
expected-expression = an expression
expected-pattern = a pattern
expected-name = a name

parse-empty-record = empty record: `{"{"}{"}"}` does not tell a type from a value
parse-precedence = precedence is a number from 0 to 9 (§4.4)
parse-mixed-record = a record either declares fields or assigns them values
parse-expected = expected { $expected }, found { $found }
parse-expected-fn = `fn` follows the ABI in `extern` (§5.3)
parse-attributed-export = an attribute goes on the definition's signature, not on `export` (§4.7)
parse-pattern-path = `{ $path }`: a path in a pattern names a constructor, and constructors are capitalised
parse-field-multiplicity = multiplicity is written on a field of a record type (`{"{"} ω x : A {"}"}`), not on a value
parse-multiplicity = multiplicity is written `0`, `1` or `ω`
parse-duplicate-state = `state`: the initial state is written twice
parse-split-clauses = clauses of `{ $name }` are separated by another declaration
parse-block-not-last = nothing follows a form with a block on its line: only indentation shows where it ends
parse-wildcard = there is no wildcard import (§4.4): opened names are listed one by one
parse-nested-import = `import` is written at the top level of a file (§4.8)
parse-too-deep = nesting deeper than the limit of { $limit }

misplaced-when = `when` belongs in a class declaration, before the superclasses: `class Ord a when Eq a where …` (§4.1)
misplaced-using = `using` belongs in an expression, before the instance: `using p (f x)` (§4.3)
misplaced-braces = braces open nothing here: an effect row is written `{"{"}Ask{"}"} A` (§3.4), a record type `{"{"}x : A{"}"}` (§4.2), a group of implicit binders `{"{"}a : Type{"}"}`; an empty row is not written
parse-misplaced = { $what }

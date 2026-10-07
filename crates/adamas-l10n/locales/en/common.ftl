# Shared by several parts of the compiler.

count-declarations = { $count ->
    [one] { $count } declaration
   *[other] { $count } declarations
}

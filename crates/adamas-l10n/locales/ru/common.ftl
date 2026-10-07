# Общее для нескольких частей компилятора.

count-declarations = { $count ->
    [one] { $count } объявление
    [few] { $count } объявления
   *[many] { $count } объявлений
}
